// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Model Checking (BMC) using z4 SMT solver
//!
//! Part of #542: BMC encodes k-step transition sequences as SAT formulas
//! to quickly find counterexamples without exhaustive state exploration.
//!
//! # BMC Formula
//!
//! For depth bound k, the BMC formula is:
//! ```text
//! Init(s0) ∧ Next(s0,s1) ∧ ... ∧ Next(sk-1,sk) ∧ (¬Safety(s0) ∨ ... ∨ ¬Safety(sk))
//! ```
//!
//! If SAT: counterexample trace exists where safety fails at some step j ≤ k.
//! If UNSAT: safety holds at all steps up to depth k.
//!
//! # Variable Unrolling
//!
//! Each state variable `x` becomes k+1 SMT variables: `x__0`, `x__1`, ..., `x__k`.
//!
//! | TLA+ | BMC encoding at step i |
//! |------|------------------------|
//! | `x` | `x__i` |
//! | `x'` | `x__i+1` |
//! | `UNCHANGED x` | `x__i+1 = x__i` |
//!
//! # Division and Modulo Restrictions (#556)
//!
//! BMC uses QF_LIA (Quantifier-Free Linear Integer Arithmetic) which does not
//! support native division or modulo. We linearize these operations as follows:
//!
//! - **Constant divisors only**: `x \div k` and `x % k` require `k` to be a literal.
//!   Variable divisors (e.g., `x \div y`) return `UntranslatableExpr` error.
//!
//! - **Positive divisors only**: Following TLC semantics, divisor must be > 0.
//!   Zero divisors return `DivisionByZero` error; negative divisors return
//!   `UnsupportedOp` error.
//!
//! - **Linearization**: `x \div k` and `x % k` introduce fresh variables `q` and `r`
//!   with constraints: `x = k*q + r ∧ 0 ≤ r < k` (Euclidean division).
//!
//! For arbitrary div/mod (non-constant or negative divisors), use the CHC/PDR
//! path in `translate.rs` which emits native solver terms.
//!
//! # Multiplication Restrictions (#771)
//!
//! QF_LIA does not support *non-linear* multiplication. In practice this means:
//! - `x * 2` is allowed (constant multiplication).
//! - `x * y` is rejected (both operands symbolic).

/// Compound type dispatch: sets, functions, cardinality in BMC context.
/// Part of #3778.
mod compound_dispatch;
/// Incremental BMC loop for iterative deepening. Part of #3724.
pub mod incremental;
/// Pure SMT-level k-induction checker for safety properties. Part of #3722.
pub mod kinduction;
/// Record and tuple encoding: per-field/per-element SMT variables. Part of #3787.
mod record_encoder;
mod translate_bmc;
mod translate_expr_impl;

use std::collections::HashMap;

// Re-exported for tests.rs (which uses `use super::*`)
#[cfg(test)]
pub(crate) use tla_core::ast::Expr;
#[cfg(test)]
pub(crate) use tla_core::Spanned;
use z4_dpll::api::{Logic, Model, SolveResult, Solver, Sort, Term};

use crate::error::{Z4Error, Z4Result, MAX_BMC_BOUND};
use crate::TlaSort;

use record_encoder::{BmcRecordVarInfo, BmcTupleVarInfo};

/// Information about a variable across all BMC steps
#[derive(Debug)]
struct BmcVarInfo {
    /// Sort of the variable
    sort: TlaSort,
    /// z4 terms for each step: index i has variable at step i
    terms: Vec<Term>,
}

/// A single state in a BMC trace
#[derive(Debug, Clone)]
pub struct BmcState {
    /// Step number (0-indexed)
    pub step: usize,
    /// Variable assignments at this step
    pub assignments: HashMap<String, BmcValue>,
}

/// A value in a BMC state
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BmcValue {
    /// Boolean value
    Bool(bool),
    /// Integer value
    Int(i64),
    /// Arbitrary-precision integer value (for values that overflow i64)
    ///
    /// Part of #3888: Avoid silently dropping big integers in extract_trace.
    BigInt(num_bigint::BigInt),
    /// Set value (finite set of elements)
    ///
    /// Part of #3778: Finite set encoding via SMT arrays.
    /// Stores the members of the set as a sorted list of values.
    Set(Vec<BmcValue>),
    /// Sequence value (ordered list of elements)
    ///
    /// Part of #3793: Sequence encoding in BMC translator.
    /// Stores elements in order (1-indexed when accessed in TLA+).
    Sequence(Vec<BmcValue>),
    /// Function value (finite mapping from Int keys to values)
    ///
    /// Part of #3786: Function encoding in BMC translator.
    /// Stores the mapping as a sorted list of (key, value) pairs.
    /// The domain is the set of keys.
    Function(Vec<(i64, BmcValue)>),
    /// Record value (finite mapping from field names to values)
    ///
    /// Part of #3787: Record encoding in BMC translator.
    /// Stores the fields as a sorted list of (field_name, value) pairs.
    Record(Vec<(String, BmcValue)>),
    /// Tuple value (ordered list of elements, 1-indexed in TLA+)
    ///
    /// Part of #3787: Tuple encoding in BMC translator.
    /// Stores elements in order (index 1 = first element).
    Tuple(Vec<BmcValue>),
}

/// Information about a function variable across all BMC steps.
///
/// Each function is encoded as two SMT arrays per step:
/// - `domain_terms[step]`: `(Array Int Bool)` — the domain membership set
/// - `mapping_terms[step]`: `(Array Int RangeSort)` — the value mapping
///
/// Part of #3786: Function encoding in BMC translator.
#[derive(Debug)]
struct BmcFuncVarInfo {
    /// Range sort of the function (retained for future introspection)
    #[allow(dead_code)]
    range_sort: TlaSort,
    /// Domain set terms per step: `(Array Int Bool)`
    domain_terms: Vec<Term>,
    /// Mapping array terms per step: `(Array Int RangeSort)`
    mapping_terms: Vec<Term>,
}

/// Information about a sequence variable across all BMC steps.
///
/// Each sequence is encoded as an SMT array (index -> element) and a
/// length term per step.
///
/// Part of #3793: Sequence encoding in BMC translator.
#[derive(Debug)]
struct BmcSeqVarInfo {
    /// Element sort of the sequence (retained for future introspection)
    #[allow(dead_code)]
    element_sort: TlaSort,
    /// Maximum sequence length (for bounding).
    max_len: usize,
    /// Array terms per step: `(Array Int ElementSort)`.
    array_terms: Vec<Term>,
    /// Length terms per step (Int).
    length_terms: Vec<Term>,
}

/// BMC translator for k-step bounded model checking
///
/// This translates TLA+ Init/Next/Safety into a BMC formula and checks it.
pub struct BmcTranslator {
    /// The z4 solver instance
    solver: Solver,
    /// Maximum bound k
    bound_k: usize,
    /// Variable info: name -> BmcVarInfo (with terms for all steps)
    vars: HashMap<String, BmcVarInfo>,
    /// Function variable info: name -> BmcFuncVarInfo (with domain+mapping per step)
    ///
    /// Part of #3786: Function encoding in BMC translator.
    func_vars: HashMap<String, BmcFuncVarInfo>,
    /// Sequence variable info: name -> BmcSeqVarInfo (array+length per step)
    ///
    /// Part of #3793: Sequence encoding in BMC translator.
    seq_vars: HashMap<String, BmcSeqVarInfo>,
    /// Record variable info: name -> BmcRecordVarInfo (per-field terms per step)
    ///
    /// Part of #3787: Record encoding in BMC translator.
    record_vars: HashMap<String, BmcRecordVarInfo>,
    /// Tuple variable info: name -> BmcTupleVarInfo (per-element terms per step)
    ///
    /// Part of #3787: Tuple encoding in BMC translator.
    tuple_vars: HashMap<String, BmcTupleVarInfo>,
    /// Current step being translated (for primed variable resolution)
    current_step: usize,
    /// Counter for generating unique auxiliary variable names (linearization)
    aux_var_counter: usize,
    /// Names of base state variables declared via `declare_var`.
    ///
    /// Used by `clear_temporary_vars` to distinguish base declarations from
    /// Skolem constants and other temporary variables injected during
    /// translation (quantifier expansion, CHOOSE, etc.). Only base vars
    /// survive `clear_temporary_vars`; temporaries are evicted.
    ///
    /// Part of #4006: prevent variable accumulation across cooperative seeds.
    base_var_names: Vec<String>,
}

impl BmcTranslator {
    /// Create a new BMC translator for bound k
    ///
    /// This creates a solver instance that will check for violations up to depth k.
    /// Uses QF_LIA logic (quantifier-free linear integer arithmetic).
    ///
    /// # Errors
    /// Returns `BmcBoundTooLarge` if k exceeds `MAX_BMC_BOUND` (100,000).
    pub fn new(k: usize) -> Z4Result<Self> {
        if k > MAX_BMC_BOUND {
            return Err(Z4Error::BmcBoundTooLarge {
                bound: k,
                max: MAX_BMC_BOUND,
            });
        }
        Ok(Self {
            solver: Solver::try_new(Logic::QfLia)?,
            bound_k: k,
            vars: HashMap::new(),
            func_vars: HashMap::new(),
            seq_vars: HashMap::new(),
            record_vars: HashMap::new(),
            tuple_vars: HashMap::new(),
            current_step: 0,
            aux_var_counter: 0,
            base_var_names: Vec::new(),
        })
    }

    /// Create a new BMC translator with array support for bound k.
    ///
    /// Uses QF_AUFLIA logic (arrays + uninterpreted functions + linear integer
    /// arithmetic), which is required when any state variable has `Set` or
    /// `Function` sort.
    ///
    /// Part of #3778: Finite set encoding via SMT arrays.
    /// Part of #3786: Function encoding via SMT arrays.
    ///
    /// # Errors
    /// Returns `BmcBoundTooLarge` if k exceeds `MAX_BMC_BOUND` (100,000).
    pub fn new_with_arrays(k: usize) -> Z4Result<Self> {
        if k > MAX_BMC_BOUND {
            return Err(Z4Error::BmcBoundTooLarge {
                bound: k,
                max: MAX_BMC_BOUND,
            });
        }
        Ok(Self {
            solver: Solver::try_new(Logic::QfAuflia)?,
            bound_k: k,
            vars: HashMap::new(),
            func_vars: HashMap::new(),
            seq_vars: HashMap::new(),
            record_vars: HashMap::new(),
            tuple_vars: HashMap::new(),
            current_step: 0,
            aux_var_counter: 0,
            base_var_names: Vec::new(),
        })
    }

    /// Declare a state variable for all k+1 steps
    ///
    /// Creates variables x__0, x__1, ..., x__k for the state variable x.
    /// Supports scalar types (Bool, Int, String), Set types, Function types,
    /// Record types, and Tuple types.
    pub fn declare_var(&mut self, name: &str, sort: TlaSort) -> Z4Result<()> {
        // Record this as a base state variable so clear_temporary_vars knows
        // to preserve it. Part of #4006.
        self.base_var_names.push(name.to_string());

        // Delegate Function sort to dedicated method
        if let TlaSort::Function { range, .. } = &sort {
            return self.declare_func_var(name, (**range).clone());
        }

        // Delegate Sequence sort to dedicated method
        if let TlaSort::Sequence {
            element_sort,
            max_len,
        } = &sort
        {
            return self.declare_seq_var(name, (**element_sort).clone(), *max_len);
        }

        // Delegate Record sort to dedicated method (Part of #3787)
        if let TlaSort::Record { field_sorts } = &sort {
            return self.declare_record_var(name, field_sorts.clone());
        }

        // Delegate Tuple sort to dedicated method (Part of #3787)
        if let TlaSort::Tuple { element_sorts } = &sort {
            return self.declare_tuple_var(name, element_sorts.clone());
        }

        if !sort.is_scalar() && !matches!(sort, TlaSort::Set { .. }) {
            return Err(Z4Error::UnsupportedOp(format!(
                "BMC only supports scalar, set, function, sequence, record, and tuple types, \
                 got {sort} for variable {name}"
            )));
        }

        let mut terms = Vec::with_capacity(self.bound_k + 1);

        // Create k+1 variables: x__0, x__1, ..., x__k
        for step in 0..=self.bound_k {
            let step_name = format!("{name}__{step}");
            let term = self.solver.declare_const(&step_name, sort.to_z4()?);
            terms.push(term);
        }

        self.vars
            .insert(name.to_string(), BmcVarInfo { sort, terms });
        Ok(())
    }

    /// Declare a function state variable for all k+1 steps.
    ///
    /// Each function is encoded as two SMT arrays per step:
    /// - `{name}__dom__{step}`: `(Array Int Bool)` — domain membership set
    /// - `{name}__map__{step}`: `(Array Int RangeSort)` — value mapping
    ///
    /// The range sort must be scalar (Bool, Int, or String).
    ///
    /// Part of #3786: Function encoding in BMC translator.
    pub fn declare_func_var(&mut self, name: &str, range_sort: TlaSort) -> Z4Result<()> {
        if self.func_vars.contains_key(name) {
            return Ok(()); // Already declared
        }

        if !range_sort.is_scalar() {
            return Err(Z4Error::UnsupportedOp(format!(
                "BMC function range must be scalar, got {range_sort} for function {name}"
            )));
        }

        let dom_sort = Sort::array(Sort::Int, Sort::Bool);
        let map_sort = Sort::array(Sort::Int, range_sort.to_z4()?);

        let mut domain_terms = Vec::with_capacity(self.bound_k + 1);
        let mut mapping_terms = Vec::with_capacity(self.bound_k + 1);

        for step in 0..=self.bound_k {
            let dom_name = format!("{name}__dom__{step}");
            let map_name = format!("{name}__map__{step}");
            domain_terms.push(self.solver.declare_const(&dom_name, dom_sort.clone()));
            mapping_terms.push(self.solver.declare_const(&map_name, map_sort.clone()));
        }

        self.func_vars.insert(
            name.to_string(),
            BmcFuncVarInfo {
                range_sort,
                domain_terms,
                mapping_terms,
            },
        );
        Ok(())
    }

    /// Get the mapping array term for a function variable at a specific step.
    ///
    /// Part of #3786.
    pub(crate) fn get_func_mapping_at_step(&self, name: &str, step: usize) -> Z4Result<Term> {
        let info = self
            .func_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {name} (at step {step})")))?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        Ok(info.mapping_terms[step])
    }

    /// Get the domain set term for a function variable at a specific step.
    ///
    /// Part of #3786.
    pub(crate) fn get_func_domain_at_step(&self, name: &str, step: usize) -> Z4Result<Term> {
        let info = self
            .func_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {name} (at step {step})")))?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        Ok(info.domain_terms[step])
    }

    /// Declare a sequence state variable for all k+1 steps.
    ///
    /// Each sequence is encoded as an SMT array + length per step:
    /// - `{name}__arr__{step}`: `(Array Int ElemSort)` — 1-indexed element storage
    /// - `{name}__len__{step}`: `Int` — current length
    ///
    /// The element sort must be scalar (Bool, Int, or String).
    /// Length is constrained to `0 <= len <= max_len` at each step.
    ///
    /// Part of #3793: Sequence encoding in BMC translator.
    pub fn declare_seq_var(
        &mut self,
        name: &str,
        element_sort: TlaSort,
        max_len: usize,
    ) -> Z4Result<()> {
        if self.seq_vars.contains_key(name) {
            return Ok(()); // Already declared
        }

        if !element_sort.is_scalar() {
            return Err(Z4Error::UnsupportedOp(format!(
                "BMC sequence element must be scalar, got {element_sort} for sequence {name}"
            )));
        }

        let arr_sort = Sort::array(Sort::Int, element_sort.to_z4()?);

        let mut array_terms = Vec::with_capacity(self.bound_k + 1);
        let mut length_terms = Vec::with_capacity(self.bound_k + 1);

        for step in 0..=self.bound_k {
            let arr_name = format!("{name}__arr__{step}");
            let len_name = format!("{name}__len__{step}");
            let arr = self.solver.declare_const(&arr_name, arr_sort.clone());
            let len = self.solver.declare_const(&len_name, Sort::Int);

            // Constrain: 0 <= len <= max_len
            let zero = self.solver.int_const(0);
            let max = self.solver.int_const(max_len as i64);
            let ge_zero = self.solver.try_ge(len, zero)?;
            let le_max = self.solver.try_le(len, max)?;
            self.solver
                .try_assert_term(ge_zero)
                .expect("invariant: ge is Bool-sorted");
            self.solver
                .try_assert_term(le_max)
                .expect("invariant: le is Bool-sorted");

            array_terms.push(arr);
            length_terms.push(len);
        }

        self.seq_vars.insert(
            name.to_string(),
            BmcSeqVarInfo {
                element_sort,
                max_len,
                array_terms,
                length_terms,
            },
        );
        Ok(())
    }

    /// Get the array term for a sequence variable at a specific step.
    ///
    /// Part of #3793.
    pub(crate) fn get_seq_array_at_step(&self, name: &str, step: usize) -> Z4Result<Term> {
        let info = self
            .seq_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("sequence {name} (at step {step})")))?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        Ok(info.array_terms[step])
    }

    /// Get the length term for a sequence variable at a specific step.
    ///
    /// Part of #3793.
    pub(crate) fn get_seq_length_at_step(&self, name: &str, step: usize) -> Z4Result<Term> {
        let info = self
            .seq_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("sequence {name} (at step {step})")))?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        Ok(info.length_terms[step])
    }

    /// Get the maximum length bound for a sequence variable.
    ///
    /// Part of #3793.
    pub(crate) fn get_seq_max_len(&self, name: &str) -> Z4Result<usize> {
        let info = self
            .seq_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("sequence {name}")))?;
        Ok(info.max_len)
    }

    /// Linearize div/mod for QF_LIA: x div k / x mod k for positive constant k.
    ///
    /// Introduces fresh variables q (quotient) and r (remainder) and asserts:
    ///   x = k*q + r ∧ 0 ≤ r < k
    ///
    /// This encodes floor division semantics (TLC-compatible):
    /// - For x = 7, k = 3:  7 = 3*2 + 1, so q = 2, r = 1
    /// - For x = -7, k = 3: -7 = 3*(-3) + 2, so q = -3, r = 2
    ///
    /// Returns (q_term, r_term) where q is the quotient and r is the remainder.
    fn linearize_div_mod(&mut self, x_term: Term, k: i64) -> Z4Result<(Term, Term)> {
        let id = self.aux_var_counter;
        self.aux_var_counter += 1;

        // Declare fresh auxiliary variables
        let q_name = format!("__div_q_{id}");
        let r_name = format!("__div_r_{id}");
        let q = self.solver.declare_const(&q_name, Sort::Int);
        let r = self.solver.declare_const(&r_name, Sort::Int);

        // Assert: x = k*q + r
        let k_term = self.solver.int_const(k);
        let k_times_q = self.solver.try_mul(k_term, q)?;
        let k_q_plus_r = self.solver.try_add(k_times_q, r)?;
        let eq = self.solver.try_eq(x_term, k_q_plus_r)?;
        self.solver.try_assert_term(eq)?;

        // Assert: 0 <= r
        let zero = self.solver.int_const(0);
        let r_ge_0 = self.solver.try_ge(r, zero)?;
        self.solver.try_assert_term(r_ge_0)?;

        // Assert: r < k
        let r_lt_k = self.solver.try_lt(r, k_term)?;
        self.solver.try_assert_term(r_lt_k)?;

        Ok((q, r))
    }

    /// Get the z4 term for a variable at a specific step
    fn get_var_at_step(&self, name: &str, step: usize) -> Z4Result<Term> {
        let info = self
            .vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("{name} (at step {step})")))?;

        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {} exceeds bound {}",
                step, self.bound_k
            )));
        }

        Ok(info.terms[step])
    }

    /// Assert a term in the solver
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

    /// Set a timeout for solver `check_sat` calls. Part of #2826.
    pub fn set_timeout(&mut self, timeout: Option<std::time::Duration>) {
        self.solver.set_timeout(timeout);
    }

    /// Get the current timeout setting.
    pub fn get_timeout(&self) -> Option<std::time::Duration> {
        self.solver.timeout()
    }

    /// Get the structured reason for the last `Unknown` result. Part of #2826.
    pub fn last_unknown_reason(&self) -> Option<z4_dpll::UnknownReason> {
        self.solver.unknown_reason()
    }

    /// Push a new assertion scope for incremental solving. Part of #3724.
    pub fn push_scope(&mut self) -> Z4Result<()> {
        Ok(self.solver.try_push()?)
    }

    /// Pop the most recent assertion scope. Part of #3724.
    pub fn pop_scope(&mut self) -> Z4Result<()> {
        Ok(self.solver.try_pop()?)
    }

    /// Remove temporary variables accumulated during translation.
    ///
    /// When the BMC translator is reused across multiple seeds in the
    /// cooperative engine, Skolem constants and other auxiliary variables
    /// are inserted into `self.vars` by quantifier expansion, CHOOSE
    /// translation, and function construction. These entries persist
    /// across `push_scope`/`pop_scope` pairs because they are HashMap
    /// entries, not solver assertions. Over many seeds, this causes the
    /// `vars` map to grow unboundedly.
    ///
    /// This method evicts all `vars` entries that are NOT in the base
    /// variable set (those declared via `declare_var`). It should be
    /// called after `pop_scope` at the end of each seed to keep the
    /// translator's variable map clean.
    ///
    /// Note: This does NOT reset `aux_var_counter`, which must remain
    /// monotonically increasing to ensure unique variable names in the
    /// solver. The solver-level declarations are harmless (the solver
    /// tracks them internally and they are lightweight); the problem is
    /// the translator-side HashMap growing without bound.
    ///
    /// Part of #4006: prevent variable accumulation across cooperative seeds.
    pub fn clear_temporary_vars(&mut self) {
        if self.base_var_names.is_empty() {
            return;
        }
        self.vars
            .retain(|name, _| self.base_var_names.contains(name));
    }

    /// Get the number of temporary variables currently in the `vars` map.
    ///
    /// Returns the count of entries in `vars` that are NOT base state
    /// variables. Useful for diagnostics and testing.
    ///
    /// Part of #4006.
    pub fn temporary_var_count(&self) -> usize {
        self.vars
            .keys()
            .filter(|name| !self.base_var_names.contains(name))
            .count()
    }

    /// Get the total number of entries in the `vars` map (base + temporary).
    ///
    /// Part of #4006.
    pub fn total_var_count(&self) -> usize {
        self.vars.len()
    }

    /// Assert concrete variable assignments at a given BMC step.
    ///
    /// Used by CDEMC to seed BMC from BFS frontier instead of Init.
    /// Each `(name, value)` pair constrains the named variable at `step`
    /// to the given concrete value. This replaces `translate_init()` when
    /// BMC starts from a known concrete state rather than the Init predicate.
    ///
    /// Part of #3765, Epic #3762.
    pub fn assert_concrete_state(
        &mut self,
        assignments: &[(String, BmcValue)],
        step: usize,
    ) -> Z4Result<()> {
        for (name, value) in assignments {
            match value {
                BmcValue::Bool(b) => {
                    let var_term = self.get_var_at_step(name, step)?;
                    let val_term = self.solver.bool_const(*b);
                    let eq = self.solver.try_eq(var_term, val_term)?;
                    self.assert(eq);
                }
                BmcValue::Int(i) => {
                    let var_term = self.get_var_at_step(name, step)?;
                    let val_term = self.solver.int_const(*i);
                    let eq = self.solver.try_eq(var_term, val_term)?;
                    self.assert(eq);
                }
                BmcValue::BigInt(n) => {
                    use num_traits::ToPrimitive;
                    let var_term = self.get_var_at_step(name, step)?;
                    let i = n.to_i64().ok_or_else(|| {
                        Z4Error::IntegerOverflow(format!(
                            "BigInt value {n} for variable '{name}' too large for solver"
                        ))
                    })?;
                    let val_term = self.solver.int_const(i);
                    let eq = self.solver.try_eq(var_term, val_term)?;
                    self.assert(eq);
                }
                BmcValue::Set(members) => {
                    let var_term = self.get_var_at_step(name, step)?;
                    // Encode a concrete set: build (store ... (const false) ... true)
                    // then assert equality with the variable.
                    let false_val = self.solver.bool_const(false);
                    let true_val = self.solver.bool_const(true);
                    let mut arr = self.solver.try_const_array(Sort::Int, false_val)?;
                    for member in members {
                        let member_term = match member {
                            BmcValue::Int(i) => self.solver.int_const(*i),
                            _ => {
                                return Err(Z4Error::UnsupportedOp(
                                    "BMC set members must be integers".to_string(),
                                ));
                            }
                        };
                        arr = self.solver.try_store(arr, member_term, true_val)?;
                    }
                    let eq = self.solver.try_eq(var_term, arr)?;
                    self.assert(eq);
                }
                BmcValue::Sequence(elements) => {
                    // Encode a concrete sequence: store elements at 1-based indices,
                    // constrain length.
                    let arr_term = self.get_seq_array_at_step(name, step)?;
                    let len_term = self.get_seq_length_at_step(name, step)?;

                    // Assert length
                    let len_val = self.solver.int_const(elements.len() as i64);
                    let len_eq = self.solver.try_eq(len_term, len_val)?;
                    self.assert(len_eq);

                    // Assert each element at its 1-based index
                    for (i, elem) in elements.iter().enumerate() {
                        let idx = self.solver.int_const((i + 1) as i64);
                        let elem_term = match elem {
                            BmcValue::Int(v) => self.solver.int_const(*v),
                            BmcValue::Bool(b) => {
                                // Bool encoded as Int: true=1, false=0
                                self.solver.int_const(if *b { 1i64 } else { 0i64 })
                            }
                            _ => {
                                return Err(Z4Error::UnsupportedOp(
                                    "BMC sequence elements must be scalars".to_string(),
                                ));
                            }
                        };
                        let selected = self.solver.try_select(arr_term, idx)?;
                        let eq = self.solver.try_eq(selected, elem_term)?;
                        self.assert(eq);
                    }
                }
                BmcValue::Function(entries) => {
                    // Encode a concrete function: constrain domain membership and
                    // mapping values. Part of #3786.
                    let dom_term = self.get_func_domain_at_step(name, step)?;
                    let map_term = self.get_func_mapping_at_step(name, step)?;

                    let false_val = self.solver.bool_const(false);
                    let true_val = self.solver.bool_const(true);

                    // Build domain: (store ... (const false) ... true)
                    let mut expected_dom = self.solver.try_const_array(Sort::Int, false_val)?;
                    for &(key, _) in entries {
                        let key_term = self.solver.int_const(key);
                        expected_dom = self.solver.try_store(expected_dom, key_term, true_val)?;
                    }
                    let dom_eq = self.solver.try_eq(dom_term, expected_dom)?;
                    self.assert(dom_eq);

                    // Constrain mapping values at each key
                    for (key, value) in entries {
                        let key_term = self.solver.int_const(*key);
                        let val_term = match value {
                            BmcValue::Int(v) => self.solver.int_const(*v),
                            BmcValue::Bool(b) => {
                                self.solver.int_const(if *b { 1i64 } else { 0i64 })
                            }
                            _ => {
                                return Err(Z4Error::UnsupportedOp(
                                    "BMC function values must be scalars".to_string(),
                                ));
                            }
                        };
                        let selected = self.solver.try_select(map_term, key_term)?;
                        let eq = self.solver.try_eq(selected, val_term)?;
                        self.assert(eq);
                    }
                }
                BmcValue::Record(fields) => {
                    // Encode a concrete record: constrain per-field variables.
                    // Part of #3787: Record encoding in BMC translator.
                    for (field_name, value) in fields {
                        let val_term = match value {
                            BmcValue::Int(v) => self.solver.int_const(*v),
                            BmcValue::Bool(b) => {
                                self.solver.int_const(if *b { 1i64 } else { 0i64 })
                            }
                            _ => {
                                return Err(Z4Error::UnsupportedOp(
                                    "BMC record field values must be scalars".to_string(),
                                ));
                            }
                        };
                        let field_term = self.get_record_field_at_step(name, field_name, step)?;
                        let eq = self.solver.try_eq(field_term, val_term)?;
                        self.assert(eq);
                    }
                }
                BmcValue::Tuple(elements) => {
                    // Encode a concrete tuple: constrain per-element variables.
                    // Part of #3787: Tuple encoding in BMC translator.
                    for (i, elem) in elements.iter().enumerate() {
                        let val_term = match elem {
                            BmcValue::Int(v) => self.solver.int_const(*v),
                            BmcValue::Bool(b) => {
                                self.solver.int_const(if *b { 1i64 } else { 0i64 })
                            }
                            _ => {
                                return Err(Z4Error::UnsupportedOp(
                                    "BMC tuple element values must be scalars".to_string(),
                                ));
                            }
                        };
                        let elem_term = self.get_tuple_element_at_step(name, i + 1, step)?;
                        let eq = self.solver.try_eq(elem_term, val_term)?;
                        self.assert(eq);
                    }
                }
            }
        }
        Ok(())
    }

    /// Assert a disjunctive wavefront formula at a given BMC step.
    ///
    /// Encodes the wavefront as:
    /// ```text
    /// shared_constraints(step) /\ (disjunct_1(step) \/ disjunct_2(step) \/ ...)
    /// ```
    ///
    /// Each shared constraint becomes `var_step = value`. Each disjunct is
    /// a conjunction of per-variable assignments for varying variables.
    /// The disjunction of all state-conjuncts encodes "the system is in
    /// one of these frontier states".
    ///
    /// This replaces N separate `assert_concrete_state` calls with a single
    /// disjunctive formula, enabling the solver to reason about the entire
    /// frontier simultaneously rather than sequentially.
    ///
    /// Part of #3794.
    pub fn assert_wavefront_formula(
        &mut self,
        shared: &[(String, BmcValue)],
        disjuncts: &[Vec<(String, BmcValue)>],
        step: usize,
    ) -> Z4Result<()> {
        // 1. Assert shared constraints directly (they hold in ALL states).
        for (name, value) in shared {
            let eq = self.make_value_eq(name, value, step)?;
            self.assert(eq);
        }

        // 2. Build the disjunction of per-state conjuncts.
        if disjuncts.is_empty() {
            return Ok(());
        }

        // Build each conjunct as AND of per-variable equalities.
        let mut disjunct_terms: Vec<Term> = Vec::with_capacity(disjuncts.len());
        for state_assignments in disjuncts {
            if state_assignments.is_empty() {
                // Empty conjunct = TRUE (all vars are shared).
                disjunct_terms.push(self.solver.bool_const(true));
                continue;
            }

            let mut conjunct_parts: Vec<Term> = Vec::with_capacity(state_assignments.len());
            for (name, value) in state_assignments {
                let eq = self.make_value_eq(name, value, step)?;
                conjunct_parts.push(eq);
            }

            // AND the parts together.
            let mut conjunct = conjunct_parts
                .pop()
                .expect("invariant: non-empty conjunct_parts");
            for part in conjunct_parts.into_iter().rev() {
                conjunct = self.solver.try_and(part, conjunct)?;
            }
            disjunct_terms.push(conjunct);
        }

        // OR the disjuncts together.
        if disjunct_terms.len() == 1 {
            // Single disjunct: assert it directly (no OR needed).
            self.assert(disjunct_terms.pop().expect("invariant: len checked == 1"));
        } else {
            let mut disjunction = disjunct_terms
                .pop()
                .expect("invariant: non-empty disjunct_terms");
            for term in disjunct_terms.into_iter().rev() {
                disjunction = self.solver.try_or(term, disjunction)?;
            }
            self.assert(disjunction);
        }

        Ok(())
    }

    /// Build an equality term `var_at_step = value` for a BmcValue.
    ///
    /// Helper for [`assert_wavefront_formula`] — handles Bool, Int, BigInt,
    /// Set, Sequence, Function, Record, and Tuple.
    ///
    /// For compound types, builds a conjunction of per-element equalities
    /// following the same encoding patterns used in [`assert_concrete_state`].
    ///
    /// Part of #3794, extended for compound types.
    fn make_value_eq(&mut self, name: &str, value: &BmcValue, step: usize) -> Z4Result<Term> {
        match value {
            BmcValue::Bool(b) => {
                let var_term = self.get_var_at_step(name, step)?;
                let val_term = self.solver.bool_const(*b);
                Ok(self.solver.try_eq(var_term, val_term)?)
            }
            BmcValue::Int(i) => {
                let var_term = self.get_var_at_step(name, step)?;
                let val_term = self.solver.int_const(*i);
                Ok(self.solver.try_eq(var_term, val_term)?)
            }
            BmcValue::BigInt(n) => {
                use num_traits::ToPrimitive;
                let var_term = self.get_var_at_step(name, step)?;
                if let Some(i) = n.to_i64() {
                    let val_term = self.solver.int_const(i);
                    Ok(self.solver.try_eq(var_term, val_term)?)
                } else {
                    Err(Z4Error::IntegerOverflow(format!(
                        "BigInt value {n} for variable '{name}' too large for wavefront encoding"
                    )))
                }
            }
            BmcValue::Set(members) => {
                // Build (store ... (const false) ... true) and assert equality
                let var_term = self.get_var_at_step(name, step)?;
                let false_val = self.solver.bool_const(false);
                let true_val = self.solver.bool_const(true);
                let mut arr = self.solver.try_const_array(Sort::Int, false_val)?;
                for member in members {
                    let member_term = match member {
                        BmcValue::Int(i) => self.solver.int_const(*i),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "wavefront set members must be integers".to_string(),
                            ));
                        }
                    };
                    arr = self.solver.try_store(arr, member_term, true_val)?;
                }
                Ok(self.solver.try_eq(var_term, arr)?)
            }
            BmcValue::Sequence(elements) => {
                // Constrain array elements and length
                let arr_term = self.get_seq_array_at_step(name, step)?;
                let len_term = self.get_seq_length_at_step(name, step)?;

                let len_val = self.solver.int_const(elements.len() as i64);
                let mut conjuncts = vec![self.solver.try_eq(len_term, len_val)?];

                for (i, elem) in elements.iter().enumerate() {
                    let idx = self.solver.int_const((i + 1) as i64);
                    let elem_term = match elem {
                        BmcValue::Int(v) => self.solver.int_const(*v),
                        BmcValue::Bool(b) => self.solver.int_const(if *b { 1i64 } else { 0i64 }),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "wavefront sequence elements must be scalars".to_string(),
                            ));
                        }
                    };
                    let selected = self.solver.try_select(arr_term, idx)?;
                    conjuncts.push(self.solver.try_eq(selected, elem_term)?);
                }

                // Fold into conjunction
                let mut result = conjuncts.pop().expect("invariant: at least length eq");
                for c in conjuncts.into_iter().rev() {
                    result = self.solver.try_and(c, result)?;
                }
                Ok(result)
            }
            BmcValue::Function(entries) => {
                // Constrain domain and mapping
                let dom_term = self.get_func_domain_at_step(name, step)?;
                let map_term = self.get_func_mapping_at_step(name, step)?;

                let false_val = self.solver.bool_const(false);
                let true_val = self.solver.bool_const(true);

                let mut expected_dom = self.solver.try_const_array(Sort::Int, false_val)?;
                for &(key, _) in entries {
                    let key_term = self.solver.int_const(key);
                    expected_dom = self.solver.try_store(expected_dom, key_term, true_val)?;
                }
                let mut conjuncts = vec![self.solver.try_eq(dom_term, expected_dom)?];

                for (key, value) in entries {
                    let key_term = self.solver.int_const(*key);
                    let val_term = match value {
                        BmcValue::Int(v) => self.solver.int_const(*v),
                        BmcValue::Bool(b) => self.solver.int_const(if *b { 1i64 } else { 0i64 }),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "wavefront function values must be scalars".to_string(),
                            ));
                        }
                    };
                    let selected = self.solver.try_select(map_term, key_term)?;
                    conjuncts.push(self.solver.try_eq(selected, val_term)?);
                }

                let mut result = conjuncts.pop().expect("invariant: at least domain eq");
                for c in conjuncts.into_iter().rev() {
                    result = self.solver.try_and(c, result)?;
                }
                Ok(result)
            }
            BmcValue::Record(fields) => {
                // Constrain per-field variables using record encoder
                let mut conjuncts = Vec::with_capacity(fields.len());
                for (field_name, value) in fields {
                    let val_term = match value {
                        BmcValue::Int(v) => self.solver.int_const(*v),
                        BmcValue::Bool(b) => self.solver.int_const(if *b { 1i64 } else { 0i64 }),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "wavefront record field values must be scalars".to_string(),
                            ));
                        }
                    };
                    let field_term = self.get_record_field_at_step(name, field_name, step)?;
                    conjuncts.push(self.solver.try_eq(field_term, val_term)?);
                }
                if conjuncts.is_empty() {
                    Ok(self.solver.bool_const(true))
                } else {
                    let mut result = conjuncts.pop().expect("invariant: non-empty");
                    for c in conjuncts.into_iter().rev() {
                        result = self.solver.try_and(c, result)?;
                    }
                    Ok(result)
                }
            }
            BmcValue::Tuple(elements) => {
                // Constrain per-element variables (1-indexed) using tuple encoder
                let mut conjuncts = Vec::with_capacity(elements.len());
                for (i, elem) in elements.iter().enumerate() {
                    let val_term = match elem {
                        BmcValue::Int(v) => self.solver.int_const(*v),
                        BmcValue::Bool(b) => self.solver.int_const(if *b { 1i64 } else { 0i64 }),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "wavefront tuple element values must be scalars".to_string(),
                            ));
                        }
                    };
                    let elem_term = self.get_tuple_element_at_step(name, i + 1, step)?;
                    conjuncts.push(self.solver.try_eq(elem_term, val_term)?);
                }
                if conjuncts.is_empty() {
                    Ok(self.solver.bool_const(true))
                } else {
                    let mut result = conjuncts.pop().expect("invariant: non-empty");
                    for c in conjuncts.into_iter().rev() {
                        result = self.solver.try_and(c, result)?;
                    }
                    Ok(result)
                }
            }
        }
    }
}

// BMC translation methods extracted to translate_bmc.rs
// TranslateExpr trait impl extracted to translate_expr_impl.rs

#[cfg(test)]
mod tests;
