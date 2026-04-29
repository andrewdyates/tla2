// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Translation from TLA+ expressions to z4 SMT solver
//!
//! This module provides the translation layer between TLA+ AST and z4's native API.
//! Unlike tla-smt which uses Z3 bindings, this uses our pure-Rust z4 SMT solver.
//!
//! # Supported TLA+ Features
//!
//! ## Phase 2a (Basic)
//! - Boolean: TRUE, FALSE, /\, \/, ~, =>, <=>
//! - Integer: literals, +, -, *, \div, %, <, <=, >, >=, =, /=
//! - Variables: state variables with Int or Bool sort
//! - Finite set membership: x \in {a, b, c}
//! - Range membership: x \in lo..hi
//!
//! ## Phase 2b (Current): Function support for finite domains
//! - Function application: <code>f\[x\]</code> for finite-domain functions
//! - Function definition: [x \in S |-> expr] over finite sets
//! - Function set membership: f \in [D -> R] for finite domains
//!
//! For finite domains, function constraints are expanded to per-element constraints.
//! This handles common TLA+ model checking patterns without requiring SMT array theory.
//!
//! ## Phase 2c (Planned)
//! - Integration with tla-check enumerate.rs
//! - SMT array theory for larger/infinite domains
//!
//! # Division and Modulo Semantics (#556, #631)
//!
//! This translator encodes TLA+ floor division/modulo using solver primitives:
//!
//! 1. **Floor division encoding** (#631): TLA+ uses floor division (rounds toward
//!    negative infinity), but z4's int_div uses truncating division (rounds toward
//!    zero). We encode floor_div as: `if signs_differ && has_remainder then trunc_div-1 else trunc_div`.
//!    Similarly, floor_mod: `if trunc_r < 0 then trunc_r + divisor else trunc_r`.
//!
//! 2. **Literal divisor validation**: For IntDiv, literal zero divisors are
//!    rejected at translation time. For Mod, literal non-positive divisors
//!    are rejected (TLC requires divisor > 0). Symbolic divisors are passed
//!    to the solver without validation.
//!
//! 3. **CHC/PDR mode only**: This translator is for CHC safety checking where
//!    the solver reasons symbolically about div/mod. For concrete evaluation,
//!    use tla-check's evaluator which enforces TLC semantics.
//!
//! For BMC mode with QF_LIA (which requires linearization), see `bmc.rs` which
//! uses a stricter approach: only constant positive divisors are supported,
//! and div/mod are expanded to fresh variables with linear constraints.
//!
//! Copyright 2026 Dropbox
//! SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::{Logic, Model, SolveResult, Solver, Sort, Term};

use tla_core::{dispatch_translate_bool, dispatch_translate_int};

use crate::error::{Z4Error, Z4Result};

/// Compound type dispatch: records, functions, finite sets, EXCEPT. Part of #3778.
mod compound_dispatch;
mod extended_ops;
/// Finite set encoding as SMT arrays (Part of #3749).
pub mod finite_set;
/// Function encoding as SMT arrays (Part of #3749).
pub mod function_encoder;
mod membership;
/// Nested powerset encoding for SUBSET(SUBSET S) patterns (Part of #3826).
pub mod nested_powerset;
/// Powerset, generalized union, and cardinality encoding (Part of Apalache parity).
pub mod powerset_encoder;
mod quantifier;
mod record;
/// Record and tuple encoding as SMT product types (Part of #3749).
pub mod record_encoder;
mod sequence;
/// Sequence encoding as SMT arrays (Part of #3793).
pub mod sequence_encoder;
mod translate_expr_impl;
mod tuple;

/// Sort (type) in the z4 context
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlaSort {
    /// Boolean sort
    Bool,
    /// Integer sort
    Int,
    /// Function sort with finite domain
    /// The domain is represented as a list of string keys (element representations)
    /// and the range sort determines the type of each element.
    Function {
        /// Domain elements as string representations
        domain_keys: Vec<String>,
        /// Sort of each range element
        range: Box<TlaSort>,
    },
    /// Tuple sort with fixed number of elements (1-indexed)
    /// Each element can have a different sort.
    Tuple {
        /// Sort of each element (1-indexed, so <code>element_sorts\[0\]</code> is element 1)
        element_sorts: Vec<TlaSort>,
    },
    /// Record sort with fixed named fields.
    Record {
        /// Sort of each field in canonical name order.
        field_sorts: Vec<(String, TlaSort)>,
    },
    /// String sort (represented via interning to integers)
    String,
    /// Set sort with known element sort.
    /// Encoded as SMT `(Array Int Bool)` via `FiniteSetEncoder`.
    Set {
        /// Sort of each element in the set.
        element_sort: Box<TlaSort>,
    },
    /// Sequence sort with known element sort and bounded length.
    /// Encoded as SMT `(Array Int ElementSort)` + an Int length variable.
    Sequence {
        /// Sort of each element in the sequence.
        element_sort: Box<TlaSort>,
        /// Maximum length bound (for finite expansion).
        max_len: usize,
    },
}

impl std::fmt::Display for TlaSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TlaSort::Bool => write!(f, "Bool"),
            TlaSort::Int => write!(f, "Int"),
            TlaSort::String => write!(f, "String"),
            TlaSort::Function { domain_keys, range } => {
                write!(f, "[{{{domain_keys:?}}} -> {range}]")
            }
            TlaSort::Tuple { element_sorts } => {
                write!(f, "<<{element_sorts:?}>>")
            }
            TlaSort::Record { field_sorts } => {
                let fields = field_sorts
                    .iter()
                    .map(|(name, sort)| format!("{name}: {sort}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{fields}]")
            }
            TlaSort::Set { element_sort } => {
                write!(f, "Set({element_sort})")
            }
            TlaSort::Sequence {
                element_sort,
                max_len,
            } => {
                write!(f, "Seq({element_sort}, max={max_len})")
            }
        }
    }
}

impl TlaSort {
    /// Canonicalize sort metadata so equivalent types compare equal.
    pub fn canonicalized(self) -> Self {
        match self {
            TlaSort::Function { domain_keys, range } => TlaSort::Function {
                domain_keys,
                range: Box::new((*range).canonicalized()),
            },
            TlaSort::Tuple { element_sorts } => TlaSort::Tuple {
                element_sorts: element_sorts
                    .into_iter()
                    .map(TlaSort::canonicalized)
                    .collect(),
            },
            TlaSort::Record { field_sorts } => {
                let mut field_sorts: Vec<(String, TlaSort)> = field_sorts
                    .into_iter()
                    .map(|(name, sort)| (name, sort.canonicalized()))
                    .collect();
                field_sorts.sort_by(|(left, _), (right, _)| left.cmp(right));
                TlaSort::Record { field_sorts }
            }
            TlaSort::Set { element_sort } => TlaSort::Set {
                element_sort: Box::new((*element_sort).canonicalized()),
            },
            TlaSort::Sequence {
                element_sort,
                max_len,
            } => TlaSort::Sequence {
                element_sort: Box::new((*element_sort).canonicalized()),
                max_len,
            },
            scalar => scalar,
        }
    }

    /// Convert TlaSort to z4 Sort for scalar types
    pub(crate) fn to_z4(&self) -> Z4Result<Sort> {
        match self {
            TlaSort::Bool => Ok(Sort::Bool),
            TlaSort::Int => Ok(Sort::Int),
            // Strings are represented as interned integers
            TlaSort::String => Ok(Sort::Int),
            // Functions are not directly mapped to z4 Sort - they're expanded
            TlaSort::Function { .. } => Err(Z4Error::UnsupportedOp(format!(
                "Function sort cannot be directly converted to z4 sort: {self}"
            ))),
            // Tuples are not directly mapped to z4 Sort - they're expanded
            TlaSort::Tuple { .. } => Err(Z4Error::UnsupportedOp(format!(
                "Tuple sort cannot be directly converted to z4 sort: {self}"
            ))),
            // Records are not directly mapped to z4 Sort - they're expanded
            TlaSort::Record { .. } => Err(Z4Error::UnsupportedOp(format!(
                "Record sort cannot be directly converted to z4 sort: {self}"
            ))),
            // Sets are represented as (Array Int Bool)
            TlaSort::Set { .. } => Ok(Sort::array(Sort::Int, Sort::Bool)),
            // Sequences are not directly mapped - they're expanded to array + length
            TlaSort::Sequence { .. } => Err(Z4Error::UnsupportedOp(format!(
                "Sequence sort cannot be directly converted to z4 sort: {self}"
            ))),
        }
    }

    /// Check if this sort represents a scalar (non-function, non-tuple) type
    pub(crate) fn is_scalar(&self) -> bool {
        matches!(self, TlaSort::Bool | TlaSort::Int | TlaSort::String)
    }
}

/// Information about a function variable with finite domain
#[derive(Debug, Clone)]
pub struct FunctionVarInfo {
    /// Domain elements as string keys
    pub domain_keys: Vec<String>,
    /// Sort of each element in the range
    pub range_sort: TlaSort,
    /// z4 terms for each domain element: key -> term
    pub element_terms: HashMap<String, Term>,
}

/// Information about a tuple variable
#[derive(Debug, Clone)]
pub struct TupleVarInfo {
    /// Sort of each element (1-indexed: <code>element_sorts\[0\]</code> is element 1)
    pub element_sorts: Vec<TlaSort>,
    /// z4 terms for each element (1-indexed: <code>element_terms\[&amp;1\]</code> is element 1)
    pub element_terms: HashMap<usize, Term>,
}

/// Information about a record variable with named fields.
/// Part of #3749: record encoding as product types.
#[derive(Debug, Clone)]
pub struct RecordVarInfo {
    /// Field sorts in canonical name order.
    pub field_sorts: Vec<(String, TlaSort)>,
    /// z4 terms for each field: field_name -> term
    pub field_terms: HashMap<String, Term>,
}

/// Information about a sequence variable with bounded length.
/// Part of #3749: sequence encoding as bounded arrays.
#[derive(Debug, Clone)]
pub struct SequenceVarInfo {
    /// Sort of each element in the sequence.
    pub element_sort: TlaSort,
    /// Maximum length bound.
    pub max_len: usize,
    /// z4 terms for each element position (1-indexed): index -> term
    pub element_terms: HashMap<usize, Term>,
    /// z4 term for the length variable.
    pub len_term: Term,
}

/// Translator from TLA+ expressions to z4 terms
pub struct Z4Translator {
    /// The z4 solver instance
    solver: Solver,
    /// Scalar variable declarations: name -> (sort, z4 term)
    vars: HashMap<String, (TlaSort, Term)>,
    /// Function variable declarations: name -> function info
    func_vars: HashMap<String, FunctionVarInfo>,
    /// Tuple variable declarations: name -> tuple info
    tuple_vars: HashMap<String, TupleVarInfo>,
    /// Record variable declarations: name -> record info. Part of #3749.
    record_vars: HashMap<String, RecordVarInfo>,
    /// Sequence variable declarations: name -> sequence info. Part of #3749.
    seq_vars: HashMap<String, SequenceVarInfo>,
    /// Array-encoded function terms: name -> FuncTerm (domain + mapping).
    ///
    /// Unlike `func_vars` (which expands functions to per-element scalar variables),
    /// this stores first-class SMT array representations. Used by `FunctionEncoder`
    /// for function construction, application, EXCEPT, DOMAIN, and equality.
    ///
    /// Part of #3786: Function encoding as SMT arrays.
    array_func_vars: HashMap<String, function_encoder::FuncTerm>,
    /// String interning table: string literal -> unique integer ID
    string_intern: HashMap<String, i64>,
    /// Constant/operator definitions for resolving Ident references in set membership.
    /// Part of #522: When translating `x \in DRINKS`, we look up `DRINKS` here.
    constant_defs: HashMap<String, Spanned<Expr>>,
    /// Track constants currently being resolved to detect circular definitions.
    /// If A == B and B == A, we detect the cycle instead of stack overflow.
    resolving_constants: std::collections::HashSet<String>,
}

/// Check if multiplication operands are non-linear (Part of #771).
///
/// Returns true if both operands are symbolic (non-constant), which
/// is unsupported under QF_LIA. Shared by Z4Translator and BmcTranslator.
pub(crate) fn is_nonlinear_mul(left: &Spanned<Expr>, right: &Spanned<Expr>) -> bool {
    let lhs_is_lit = matches!(&left.node, Expr::Int(_))
        || matches!(
            &left.node,
            Expr::Neg(inner) if matches!(&inner.node, Expr::Int(_))
        );
    let rhs_is_lit = matches!(&right.node, Expr::Int(_))
        || matches!(
            &right.node,
            Expr::Neg(inner) if matches!(&inner.node, Expr::Int(_))
        );
    !lhs_is_lit && !rhs_is_lit
}

impl Z4Translator {
    /// Create a new translator using QF_LIA logic (quantifier-free linear integer arithmetic)
    pub fn new() -> Self {
        Self {
            solver: Solver::try_new(Logic::QfLia).expect("invariant: QfLia is a valid logic"),
            vars: HashMap::new(),
            func_vars: HashMap::new(),
            tuple_vars: HashMap::new(),
            record_vars: HashMap::new(),
            seq_vars: HashMap::new(),
            array_func_vars: HashMap::new(),
            string_intern: HashMap::new(),
            constant_defs: HashMap::new(),
            resolving_constants: std::collections::HashSet::new(),
        }
    }

    /// Create a new translator using QF_AUFLIA logic (arrays + UF + linear integer arithmetic).
    ///
    /// Required for finite set encoding via SMT arrays (Part of #3749).
    /// Use this constructor when translating expressions that involve
    /// set operations (`Union`, `Intersect`, `SetMinus`, `Subseteq`, `Cardinality`).
    pub fn new_with_arrays() -> Self {
        Self {
            solver: Solver::try_new(Logic::QfAuflia).expect("invariant: QfAuflia is a valid logic"),
            vars: HashMap::new(),
            func_vars: HashMap::new(),
            tuple_vars: HashMap::new(),
            record_vars: HashMap::new(),
            seq_vars: HashMap::new(),
            array_func_vars: HashMap::new(),
            string_intern: HashMap::new(),
            constant_defs: HashMap::new(),
            resolving_constants: std::collections::HashSet::new(),
        }
    }

    /// Set constant/operator definitions for resolving Ident references.
    ///
    /// Part of #522: When the translator encounters `x \in DRINKS` where `DRINKS`
    /// is a named constant, it looks up the definition here and translates that.
    pub fn set_constant_defs(&mut self, defs: HashMap<String, Spanned<Expr>>) {
        self.constant_defs = defs;
    }

    /// Declare a variable with the given sort
    pub fn declare_var(&mut self, name: &str, sort: TlaSort) -> Z4Result<Term> {
        if let Some((existing_sort, _)) = self.vars.get(name) {
            if existing_sort != &sort {
                return Err(Z4Error::TypeMismatch {
                    name: name.to_string(),
                    expected: format!("{existing_sort}"),
                    actual: format!("{sort}"),
                });
            }
            return Ok(self.vars[name].1);
        }

        let term = self.solver.declare_const(name, sort.to_z4()?);
        self.vars.insert(name.to_string(), (sort, term));
        Ok(term)
    }

    /// Get a declared variable's term
    pub fn get_var(&self, name: &str) -> Z4Result<(TlaSort, Term)> {
        self.vars
            .get(name)
            .cloned()
            .ok_or_else(|| Z4Error::UnknownVariable(name.to_string()))
    }

    /// Declare a function variable with finite domain
    ///
    /// Creates individual z4 variables for each domain element.
    /// For example, `declare_func_var("f", ["a", "b"], TlaSort::Int)` creates
    /// variables "f__a" and "f__b" of sort Int.
    pub fn declare_func_var(
        &mut self,
        name: &str,
        domain_keys: Vec<String>,
        range_sort: TlaSort,
    ) -> Z4Result<()> {
        if self.func_vars.contains_key(name) {
            return Ok(()); // Already declared
        }
        if !range_sort.is_scalar() {
            return Err(Z4Error::UnsupportedOp(
                "nested function types not yet supported".to_string(),
            ));
        }

        let mut element_terms = HashMap::new();
        for key in &domain_keys {
            let var_name = format!("{name}__{key}");
            let term = if let Some((existing_sort, term)) = self.vars.get(&var_name) {
                if existing_sort != &range_sort {
                    return Err(Z4Error::TypeMismatch {
                        name: var_name,
                        expected: format!("{existing_sort}"),
                        actual: format!("{range_sort}"),
                    });
                }
                *term
            } else {
                let term = self.solver.declare_const(&var_name, range_sort.to_z4()?);
                self.vars.insert(var_name, (range_sort.clone(), term));
                term
            };
            element_terms.insert(key.clone(), term);
        }

        self.func_vars.insert(
            name.to_string(),
            FunctionVarInfo {
                domain_keys,
                range_sort,
                element_terms,
            },
        );
        Ok(())
    }

    /// Get a function variable's info
    pub fn get_func_var(&self, name: &str) -> Z4Result<&FunctionVarInfo> {
        self.func_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {name}")))
    }

    /// Declare a tuple variable with the given element sorts
    ///
    /// Creates individual z4 variables for each element.
    /// For example, `declare_tuple_var("t", [Int, Int, Bool])` creates
    /// variables "t__1" (Int), "t__2" (Int), and "t__3" (Bool).
    /// TLA+ tuples use 1-based indexing.
    pub fn declare_tuple_var(&mut self, name: &str, element_sorts: Vec<TlaSort>) -> Z4Result<()> {
        if self.tuple_vars.contains_key(name) {
            return Ok(()); // Already declared
        }
        if element_sorts.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "empty tuple not supported".to_string(),
            ));
        }
        for sort in &element_sorts {
            if !sort.is_scalar() {
                return Err(Z4Error::UnsupportedOp(
                    "nested tuple/function types not yet supported".to_string(),
                ));
            }
        }

        let mut element_terms = HashMap::new();
        for (i, sort) in element_sorts.iter().enumerate() {
            let idx = i + 1; // 1-based indexing
            let var_name = format!("{name}__{idx}");
            let term = if let Some((existing_sort, term)) = self.vars.get(&var_name) {
                if existing_sort != sort {
                    return Err(Z4Error::TypeMismatch {
                        name: var_name,
                        expected: format!("{existing_sort}"),
                        actual: format!("{sort}"),
                    });
                }
                *term
            } else {
                let term = self.solver.declare_const(&var_name, sort.to_z4()?);
                self.vars.insert(var_name, (sort.clone(), term));
                term
            };
            element_terms.insert(idx, term);
        }

        self.tuple_vars.insert(
            name.to_string(),
            TupleVarInfo {
                element_sorts,
                element_terms,
            },
        );
        Ok(())
    }

    /// Get a tuple variable's info
    pub fn get_tuple_var(&self, name: &str) -> Z4Result<&TupleVarInfo> {
        self.tuple_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("tuple {name}")))
    }

    /// Get the z4 term for a tuple element access <code>t\[i\]</code>
    /// where i is a 1-based index
    pub fn get_tuple_element(&self, tuple_name: &str, index: usize) -> Z4Result<Term> {
        let info = self.get_tuple_var(tuple_name)?;
        info.element_terms.get(&index).copied().ok_or_else(|| {
            Z4Error::UnsupportedOp(format!(
                "tuple index {} out of bounds (tuple has {} elements)",
                index,
                info.element_sorts.len()
            ))
        })
    }

    /// Get the z4 term for a function application <code>f\[key\]</code>
    /// where key is a string representation of the argument
    pub fn get_func_element(&self, func_name: &str, key: &str) -> Z4Result<Term> {
        let info = self.get_func_var(func_name)?;
        info.element_terms
            .get(key)
            .copied()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("{func_name}[{key}]")))
    }

    /// Declare a record variable with the given field sorts.
    ///
    /// Creates individual z4 variables for each field.
    /// For example, `declare_record_var("r", [("a", Int), ("b", Bool)])` creates
    /// variables "r__a" (Int) and "r__b" (Bool).
    ///
    /// Supports nested compound types in fields:
    /// - `Set(element_sort)` fields are declared as `(Array Int Bool)` SMT variables.
    /// - `Record(sub_fields)` fields recursively declare a sub-record named
    ///   `{name}__{field_name}` in `record_vars` with flattened sub-field variables.
    ///   Use [`get_nested_record_name`] to resolve the child record name.
    ///
    /// Part of #3749.
    pub fn declare_record_var(
        &mut self,
        name: &str,
        field_sorts: Vec<(String, TlaSort)>,
    ) -> Z4Result<()> {
        if self.record_vars.contains_key(name) {
            return Ok(()); // Already declared
        }
        if field_sorts.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "empty record not supported".to_string(),
            ));
        }
        for (field_name, sort) in &field_sorts {
            if !sort.is_scalar()
                && !matches!(sort, TlaSort::Set { .. })
                && !matches!(sort, TlaSort::Record { .. })
            {
                return Err(Z4Error::UnsupportedOp(format!(
                    "unsupported compound type {sort} in record field '{field_name}'"
                )));
            }
        }

        let mut field_terms = HashMap::new();
        for (field_name, sort) in &field_sorts {
            let var_name = format!("{name}__{field_name}");
            match sort {
                TlaSort::Record {
                    field_sorts: sub_fields,
                } => {
                    // Recursively declare a sub-record with flattened naming.
                    // The sub-record is registered as "{name}__{field_name}" in record_vars.
                    self.declare_record_var(&var_name, sub_fields.clone())?;
                    // Store a sentinel boolean const so field_terms has an entry.
                    // Callers operating on nested record fields should use
                    // get_nested_record_name() instead of this term directly.
                    let sentinel = self.solver.bool_const(true);
                    field_terms.insert(field_name.clone(), sentinel);
                }
                _ => {
                    // Scalar or Set: declare directly (Set maps to (Array Int Bool))
                    let term = if let Some((existing_sort, term)) = self.vars.get(&var_name) {
                        if existing_sort != sort {
                            return Err(Z4Error::TypeMismatch {
                                name: var_name,
                                expected: format!("{existing_sort}"),
                                actual: format!("{sort}"),
                            });
                        }
                        *term
                    } else {
                        let term = self.solver.declare_const(&var_name, sort.to_z4()?);
                        self.vars.insert(var_name, (sort.clone(), term));
                        term
                    };
                    field_terms.insert(field_name.clone(), term);
                }
            }
        }

        self.record_vars.insert(
            name.to_string(),
            RecordVarInfo {
                field_sorts,
                field_terms,
            },
        );
        Ok(())
    }

    /// Get the nested record variable name for a record field of type `Record`.
    ///
    /// When a record `r` has a field `msgs` of type `Record(...)`, the sub-record
    /// is declared as `r__msgs` in `record_vars`. This method returns that name.
    ///
    /// Returns `None` if the field is not of type `Record`.
    pub fn get_nested_record_name(&self, record_name: &str, field_name: &str) -> Option<String> {
        let info = self.record_vars.get(record_name)?;
        let is_record_field = info
            .field_sorts
            .iter()
            .any(|(name, sort)| name == field_name && matches!(sort, TlaSort::Record { .. }));
        if is_record_field {
            Some(format!("{record_name}__{field_name}"))
        } else {
            None
        }
    }

    /// Get a record variable's info.
    pub fn get_record_var(&self, name: &str) -> Z4Result<&RecordVarInfo> {
        self.record_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record {name}")))
    }

    /// Get the z4 term for a record field access `r.field`.
    pub fn get_record_field(&self, record_name: &str, field_name: &str) -> Z4Result<Term> {
        let info = self.get_record_var(record_name)?;
        info.field_terms
            .get(field_name)
            .copied()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("{record_name}.{field_name}")))
    }

    /// Declare a sequence variable with bounded length.
    ///
    /// Creates individual z4 variables for each element position and a length variable.
    /// For example, `declare_seq_var("s", TlaSort::Int, 5)` creates
    /// variables "s__1"..."s__5" (Int) and "s__len" (Int).
    /// Part of #3749.
    pub fn declare_seq_var(
        &mut self,
        name: &str,
        element_sort: TlaSort,
        max_len: usize,
    ) -> Z4Result<()> {
        if self.seq_vars.contains_key(name) {
            return Ok(()); // Already declared
        }
        if max_len == 0 {
            return Err(Z4Error::UnsupportedOp(
                "sequence with max_len=0 not supported".to_string(),
            ));
        }
        if !element_sort.is_scalar() {
            return Err(Z4Error::UnsupportedOp(
                "nested compound types in sequence elements not yet supported".to_string(),
            ));
        }

        let mut element_terms = HashMap::new();
        for idx in 1..=max_len {
            let var_name = format!("{name}__{idx}");
            let term = self.solver.declare_const(&var_name, element_sort.to_z4()?);
            self.vars.insert(var_name, (element_sort.clone(), term));
            element_terms.insert(idx, term);
        }

        // Declare length variable with constraint: 0 <= len <= max_len
        let len_var_name = format!("{name}__len");
        let len_term = self.solver.declare_const(&len_var_name, Sort::Int);
        self.vars.insert(len_var_name, (TlaSort::Int, len_term));

        let zero = self.solver.int_const(0);
        let max = self.solver.int_const(max_len as i64);
        let ge_zero = self
            .solver
            .try_ge(len_term, zero)
            .expect("invariant: ge requires Int terms");
        let le_max = self
            .solver
            .try_le(len_term, max)
            .expect("invariant: le requires Int terms");
        self.assert(ge_zero);
        self.assert(le_max);

        self.seq_vars.insert(
            name.to_string(),
            SequenceVarInfo {
                element_sort,
                max_len,
                element_terms,
                len_term,
            },
        );
        Ok(())
    }

    /// Get a sequence variable's info.
    pub fn get_seq_var(&self, name: &str) -> Z4Result<&SequenceVarInfo> {
        self.seq_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("sequence {name}")))
    }

    /// Store an array-encoded function term under the given name.
    ///
    /// This is used by the `FunctionEncoder` integration path to register
    /// functions created by `[x \in S |-> e]` so that subsequent operations
    /// (`f[x]`, `DOMAIN f`, `[f EXCEPT ![a] = b]`, `f = g`) can look up the
    /// domain and mapping arrays.
    ///
    /// Part of #3786: Function encoding as SMT arrays.
    pub(crate) fn store_array_func(&mut self, name: &str, func_term: function_encoder::FuncTerm) {
        self.array_func_vars.insert(name.to_string(), func_term);
    }

    /// Get an array-encoded function term by name.
    ///
    /// Part of #3786.
    pub(crate) fn get_array_func(&self, name: &str) -> Option<&function_encoder::FuncTerm> {
        self.array_func_vars.get(name)
    }

    /// Intern a string literal, returning its unique integer ID.
    ///
    /// Used by the record encoder to convert field names to SMT integers
    /// for DOMAIN encoding. Part of #3787.
    pub(crate) fn intern_string(&mut self, s: &str) -> i64 {
        if let Some(&id) = self.string_intern.get(s) {
            id
        } else {
            let id = self.string_intern.len() as i64 + 1;
            self.string_intern.insert(s.to_string(), id);
            id
        }
    }

    /// Add an assertion to the solver
    pub fn assert(&mut self, term: Term) {
        self.solver
            .try_assert_term(term)
            .expect("invariant: assert requires Bool-sorted term");
    }

    /// Check satisfiability
    pub fn check_sat(&mut self) -> SolveResult {
        self.solver.check_sat().into_inner()
    }

    /// Check satisfiability with panic protection.
    ///
    /// Uses the upstream `try_check_sat()` API to catch solver panics and
    /// return them as `Z4Error::Solver(SolverError::SolverPanic(...))`.
    /// Part of #2826.
    pub fn try_check_sat(&mut self) -> Z4Result<SolveResult> {
        Ok(self.solver.try_check_sat()?.into_inner())
    }

    /// Get the model if SAT
    pub fn get_model(&mut self) -> Option<Model> {
        self.solver.model().map(z4_dpll::VerifiedModel::into_inner)
    }

    /// Get the model with error reporting.
    ///
    /// Uses the upstream `try_get_model()` API to return typed errors
    /// (no result, not SAT, model generation failed) instead of `None`.
    /// Part of #2826.
    pub fn try_get_model(&self) -> Z4Result<Model> {
        Ok(self.solver.try_get_model()?.into_inner())
    }

    /// Set a timeout for solver `check_sat` calls.
    ///
    /// When a timeout is set, `check_sat()` / `try_check_sat()` will return
    /// `SolveResult::Unknown` if the solver exceeds the time limit.
    /// Use `last_unknown_reason()` to distinguish timeout from other causes.
    /// Part of #2826.
    pub fn set_timeout(&mut self, timeout: Option<std::time::Duration>) {
        self.solver.set_timeout(timeout);
    }

    /// Get the current timeout setting.
    pub fn get_timeout(&self) -> Option<std::time::Duration> {
        self.solver.timeout()
    }

    /// Get the structured reason for the last `Unknown` result.
    ///
    /// Returns `Some(UnknownReason::Timeout)` when the solver timed out,
    /// `Some(UnknownReason::Interrupted)` for external interrupts, etc.
    /// Part of #2826.
    pub fn last_unknown_reason(&self) -> Option<z4_dpll::UnknownReason> {
        self.solver.unknown_reason()
    }

    /// Get the reverse string interning map (ID -> String).
    ///
    /// Used by z4_enumerate to convert model integer values back to strings.
    pub fn get_string_reverse_map(&self) -> HashMap<i64, String> {
        self.string_intern
            .iter()
            .map(|(s, &id)| (id, s.clone()))
            .collect()
    }

    /// Translate a TLA+ expression to a z4 boolean term.
    ///
    /// Routes through shared dispatch ([`dispatch_translate_bool`]) for common
    /// arms (And/Or/Not/Implies/Equiv/Eq/Neq/Lt/Leq/Gt/Geq/If/Bool/Ident).
    /// Backend-specific arms (Forall/Exists/In/FuncApply/ModuleRef) are handled
    /// via [`tla_core::TranslateExpr::translate_bool_extended`].
    pub fn translate_bool(&mut self, expr: &Spanned<Expr>) -> Z4Result<Term> {
        dispatch_translate_bool(self, expr)
    }

    /// Translate a TLA+ expression to a z4 integer term.
    ///
    /// Routes through shared dispatch ([`dispatch_translate_int`]) for common
    /// arms (Int/Ident/Add/Sub/Neg/If). Backend-specific arms
    /// (Mul with non-linear guard, IntDiv with floor-div, Mod with floor-mod,
    /// FuncApply) are handled via [`tla_core::TranslateExpr::translate_int_extended`].
    pub fn translate_int(&mut self, expr: &Spanned<Expr>) -> Z4Result<Term> {
        dispatch_translate_int(self, expr)
    }

    // Module ref, floor div/mod, string translation, and collect_conjuncts
    // extracted to extended_ops.rs. Set membership, function application,
    // tuple operations, and quantifier expansion in membership.rs, tuple.rs, quantifier.rs.
}

#[cfg(test)]
mod tests;
