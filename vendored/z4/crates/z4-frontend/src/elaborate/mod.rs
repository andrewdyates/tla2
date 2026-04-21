// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elaboration: convert parsed terms to internal representation
//!
//! This module bridges the parser's AST to the core term representation.
//! It handles:
//! - Sort conversion
//! - Term internalization into the hash-consed store
//! - Symbol table management
//! - Let-binding expansion

use crate::command::Term as ParsedTerm;
use hashbrown::HashMap;
use z4_core::{Sort, TermId, TermStore};

/// The reserved prefix for internal Z4 symbols.
/// User declarations with this prefix are rejected.
pub(crate) const INTERNAL_SYMBOL_PREFIX: &str = "__z4_";

/// Check if a symbol name uses the reserved internal prefix.
pub(crate) fn is_reserved_symbol(name: &str) -> bool {
    name.starts_with(INTERNAL_SYMBOL_PREFIX)
}

/// Error during elaboration
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ElaborateError {
    /// Undefined symbol
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),
    /// Sort mismatch
    #[error("sort mismatch: expected {expected}, got {actual}")]
    SortMismatch {
        /// The expected sort
        expected: String,
        /// The actual sort found
        actual: String,
    },
    /// Invalid constant
    #[error("invalid constant: {0}")]
    InvalidConstant(String),
    /// Unsupported feature
    #[error("unsupported: {0}")]
    Unsupported(String),
    /// Reserved symbol
    #[error("symbol '{0}' uses reserved prefix '{INTERNAL_SYMBOL_PREFIX}' - ")]
    ReservedSymbol(String),
    /// Scope underflow (pop with no matching push)
    #[error("scope underflow: pop called with no matching push")]
    ScopeUnderflow,
}

/// Result type for elaboration
pub(crate) type Result<T> = std::result::Result<T, ElaborateError>;

/// Symbol information
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SymbolInfo {
    /// The term ID if it's a constant
    pub term: Option<TermId>,
    /// The sort of the symbol
    pub sort: Sort,
    /// Argument sorts (empty for constants)
    pub arg_sorts: Vec<Sort>,
}

/// Optimization direction for an objective term
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveDirection {
    /// Maximize the objective
    Maximize,
    /// Minimize the objective
    Minimize,
}

/// An optimization objective
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Objective {
    /// Whether to maximize or minimize
    pub direction: ObjectiveDirection,
    /// The objective term
    pub term: TermId,
}

/// Elaboration context
pub struct Context {
    /// The term store
    pub terms: TermStore,
    /// Symbol table: name -> info
    symbols: HashMap<String, SymbolInfo>,
    /// Overloaded declared symbols keyed by surface name.
    ///
    /// Datatype selectors may legally reuse the same surface name across
    /// different datatypes, so elaboration must resolve them by argument sort.
    overloaded_symbols: HashMap<String, Vec<SymbolInfo>>,
    /// Sort definitions: name -> sort
    sort_defs: HashMap<String, Sort>,
    /// Function definitions: name -> (params, body)
    fun_defs: HashMap<String, (Vec<(String, Sort)>, ParsedTerm)>,
    /// Datatype definitions: dt_name -> constructor_names
    datatypes: HashMap<String, Vec<String>>,
    /// Constructor to datatype map: ctor_name -> (dt_name, ctor_name)
    constructors: HashMap<String, (String, String)>,
    /// Constructor to selectors map: ctor_name -> selector_names (positional)
    ctor_selectors: HashMap<String, Vec<String>>,
    /// Constructor to selector metadata (name + return sort) in declaration order.
    ctor_selector_info: HashMap<String, Vec<(String, Sort)>>,
    /// Current logic
    logic: Option<String>,
    /// Assertions (internal normalized form)
    pub assertions: Vec<TermId>,
    /// Assertions in their original parsed form (before internal normalization)
    ///
    /// This is used to align exported proofs with the surface syntax of the input file.
    /// For example, Z4 internally canonicalizes `(>= a b)` into `(<= b a)` for hashing
    /// and solver simplicity, but proof checkers match `assume` steps against the
    /// original problem premises.
    assertions_parsed: Vec<ParsedTerm>,
    /// Optimization objectives (from maximize/minimize)
    objectives: Vec<Objective>,
    /// Scope stack for push/pop
    scopes: Vec<ScopeFrame>,
    /// Solver options (keyword -> value)
    options: HashMap<String, OptionValue>,
    /// Named formulas: name -> term_id (for get-assignment and get-unsat-core)
    named_terms: HashMap<String, TermId>,
}

/// Value for a solver option
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OptionValue {
    /// Boolean option
    Bool(bool),
    /// String option
    String(String),
    /// Numeric option
    Numeral(String),
}

/// A scope frame for push/pop
#[derive(Debug, Clone, Default)]
struct ScopeFrame {
    /// Symbols defined in this scope
    symbols: Vec<String>,
    /// Number of assertions before this scope
    assertion_count: usize,
    /// Number of objectives before this scope
    objective_count: usize,
    /// Named terms defined in this scope
    named_terms: Vec<String>,
    /// Datatypes defined in this scope
    datatypes: Vec<String>,
    /// Constructors defined in this scope
    constructors: Vec<String>,
    /// Sort definitions in this scope
    sort_defs: Vec<String>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// Create a new elaboration context
    pub fn new() -> Self {
        let mut options = HashMap::new();
        // Default options per SMT-LIB 2.6 standard
        options.insert("print-success".to_string(), OptionValue::Bool(false));
        options.insert("produce-models".to_string(), OptionValue::Bool(true));
        options.insert("produce-unsat-cores".to_string(), OptionValue::Bool(false));
        options.insert("produce-proofs".to_string(), OptionValue::Bool(false));
        options.insert("produce-assignments".to_string(), OptionValue::Bool(false));
        options.insert(
            "random-seed".to_string(),
            OptionValue::Numeral("0".to_string()),
        );

        Self {
            terms: TermStore::new(),
            symbols: HashMap::new(),
            overloaded_symbols: HashMap::new(),
            sort_defs: HashMap::new(),
            fun_defs: HashMap::new(),
            datatypes: HashMap::new(),
            constructors: HashMap::new(),
            ctor_selectors: HashMap::new(),
            ctor_selector_info: HashMap::new(),
            logic: None,
            assertions: Vec::new(),
            assertions_parsed: Vec::new(),
            objectives: Vec::new(),
            scopes: Vec::new(),
            options,
            named_terms: HashMap::new(),
        }
    }

    /// Get the current logic setting.
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Set the logic for this context.
    pub fn set_logic(&mut self, logic: String) {
        self.logic = Some(logic);
    }

    /// Get the parsed assertions (original surface syntax).
    pub fn assertions_parsed(&self) -> &[ParsedTerm] {
        &self.assertions_parsed
    }

    /// Return the minimum active SMT scope depth for each asserted term.
    ///
    /// Depth `0` is the global scope. If the same assertion term is present in
    /// multiple active scopes, the shallowest active depth wins because that is
    /// the scope where its activation must survive after pop().
    pub fn active_assertion_min_scope_depths(&self) -> HashMap<TermId, usize> {
        let mut depths = HashMap::new();
        let mut scope_boundaries: Vec<usize> = self
            .scopes
            .iter()
            .map(|frame| frame.assertion_count)
            .collect();
        scope_boundaries.push(self.assertions.len());

        let mut depth = 0usize;
        let mut next_boundary_idx = 0usize;
        let mut next_boundary = scope_boundaries
            .get(next_boundary_idx)
            .copied()
            .unwrap_or(self.assertions.len());

        for (idx, &assertion) in self.assertions.iter().enumerate() {
            while idx >= next_boundary && next_boundary_idx + 1 < scope_boundaries.len() {
                depth += 1;
                next_boundary_idx += 1;
                next_boundary = scope_boundaries[next_boundary_idx];
            }
            depths
                .entry(assertion)
                .and_modify(|existing: &mut usize| *existing = (*existing).min(depth))
                .or_insert(depth);
        }

        depths
    }

    /// Push an assertion and its parsed form together, keeping them aligned.
    pub fn add_assertion_with_parsed(&mut self, term: TermId, parsed: ParsedTerm) {
        self.assertions.push(term);
        self.assertions_parsed.push(parsed);
    }

    /// Get the optimization objectives.
    pub fn objectives(&self) -> &[Objective] {
        &self.objectives
    }

    /// Add an optimization objective.
    pub fn add_objective(&mut self, objective: Objective) {
        self.objectives.push(objective);
    }
}

/// Result of processing a command that requires action
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CommandResult {
    /// Need to run check-sat
    CheckSat,
    /// Need to run check-sat with assumptions
    CheckSatAssuming(Vec<TermId>),
    /// Need to produce a model
    GetModel,
    /// Need to produce objective values (for maximize/minimize)
    GetObjectives,
    /// Need to produce values for specific terms
    GetValue(Vec<TermId>),
    /// Need to get solver info
    GetInfo(String),
    /// Need to get an option value
    GetOption(String),
    /// Need to get current assertions
    GetAssertions,
    /// Need to print a string (echo command)
    Echo(String),
    /// Need to get assignment of named formulas
    GetAssignment,
    /// Need to get unsatisfiable core
    GetUnsatCore,
    /// Need to get unsatisfiable assumptions (from check-sat-assuming)
    GetUnsatAssumptions,
    /// Need to get proof
    GetProof,
    /// Exit the solver
    Exit,
    /// Need to simplify a term
    Simplify(TermId),
}

mod app;
mod commands;
mod datatypes;
mod declarations;
mod indexed;
mod qualified;
mod sorts;
mod term;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
