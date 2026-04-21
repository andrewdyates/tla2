// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model and value extraction: unsat assumptions, model*, value*,
//! declared_variables.

use std::collections::HashMap;

use z4_core::TermId;
use z4_frontend::sexp::{parse_sexp, SExpr};

use crate::api::model_parse;
use crate::api::types::{ModelValue, SolveResult, SolverError, Term, VerifiedModel};
use crate::api::Solver;

impl Solver {
    /// Subset of assumptions that caused the last UNSAT result.
    ///
    /// After `check_sat_assuming()` returns `SolveResult::Unsat`, this method
    /// returns the assumptions that contributed to unsatisfiability.
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - The last check was `check_sat()` not `check_sat_assuming()`
    ///
    /// # Note
    ///
    /// The current implementation returns all assumptions. A future optimization
    /// will track which assumptions were actually needed by analyzing the proof.
    #[must_use]
    pub fn unsat_assumptions(&self) -> Option<Vec<Term>> {
        // Check that last result was unsat
        let last_result = self.executor.last_result()?;
        if last_result != SolveResult::Unsat {
            return None;
        }

        // Return the stored assumptions (mapped back to Terms)
        // Sort by TermId for deterministic ordering (#3060)
        self.last_assumptions.as_ref().map(|assumptions| {
            let mut sorted: Vec<_> = assumptions.iter().collect();
            sorted.sort_unstable_by_key(|(tid, _)| tid.0);
            sorted.into_iter().map(|(_, term)| *term).collect()
        })
    }

    /// Deprecated: use [`unsat_assumptions`](Self::unsat_assumptions) instead.
    #[deprecated(since = "0.3.0", note = "Use unsat_assumptions() instead")]
    #[must_use]
    pub fn get_unsat_assumptions(&self) -> Option<Vec<Term>> {
        self.unsat_assumptions()
    }

    /// Unsat core: names of assertions that caused the last UNSAT result.
    ///
    /// Requires `:produce-unsat-cores` to be enabled via
    /// `solver.set_option(":produce-unsat-cores", "true")`.
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - Unsat core production is not enabled
    /// - No named assertions were asserted
    #[must_use]
    pub fn unsat_core(&self) -> Option<Vec<String>> {
        self.try_get_unsat_core().ok()
    }

    /// Deprecated: use [`unsat_core`](Self::unsat_core) instead.
    #[deprecated(since = "0.3.0", note = "Use unsat_core() instead")]
    #[must_use]
    pub fn get_unsat_core(&self) -> Option<Vec<String>> {
        self.unsat_core()
    }

    /// Fallible version of [`unsat_core`](Self::unsat_core).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotUnsat`] — last result was not UNSAT
    /// - [`SolverError::UnsatCoreGenerationFailed`] — core generation failed
    ///
    /// The returned names are drawn from the currently active named
    /// assertions. Treat the core as an explanation subset, not as a
    /// minimum-cardinality certificate: callers may rely on membership checks
    /// such as "is `negated_postcondition` present?", but should not depend on
    /// the exact number or ordering of names beyond the stable string values.
    ///
    /// # Known Limitations
    ///
    /// - **Core minimality:** The core is an over-approximation derived from
    ///   the SAT solver's assumption-based UNSAT analysis. It is sound (every
    ///   name in the core contributed to UNSAT) but may not be minimal.
    /// - **Quantifier interaction:** Unsat cores for quantified formulas may
    ///   include names that were used during E-matching or quantifier
    ///   instantiation, even if a tighter core exists.
    /// - **Push/pop scope:** Named assertions follow scope semantics. After
    ///   `pop()`, any named assertions from the popped scope are discarded and
    ///   will not appear in subsequent cores.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_unsat_core(&self) -> Result<Vec<String>, SolverError> {
        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if last_result != SolveResult::Unsat {
            return Err(SolverError::NotUnsat);
        }

        let core_output = self.executor.unsat_core();
        if core_output.starts_with("(error ") {
            return Err(SolverError::UnsatCoreGenerationFailed(core_output));
        }

        let parsed = parse_sexp(&core_output).map_err(|err| {
            SolverError::UnsatCoreGenerationFailed(format!(
                "failed to parse unsat core `{core_output}`: {err}"
            ))
        })?;

        match &parsed {
            SExpr::List(items) => items
                .iter()
                .map(|item| match item {
                    SExpr::Symbol(name) => Ok(name.clone()),
                    other => Err(SolverError::UnsatCoreGenerationFailed(format!(
                        "expected symbol in unsat core, got {other}"
                    ))),
                })
                .collect(),
            other => Err(SolverError::UnsatCoreGenerationFailed(format!(
                "expected list-valued unsat core, got {other}"
            ))),
        }
    }

    /// Raw SMT-LIB model string from the last SAT result.
    ///
    /// Returns the unparsed model output in SMT-LIB format. This is useful when:
    /// - You need to access array or uninterpreted function values (not yet parsed by `model`)
    /// - You want to log/debug the raw model output
    /// - You're implementing custom model parsing
    ///
    /// Returns `None` if the last check was not `Sat` or if model generation is unavailable.
    ///
    /// # Example
    ///
    /// ```
    /// # use z4_dpll::api::{Solver, Sort, Logic, SolveResult};
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let five = solver.int_const(5);
    /// let eq = solver.eq(x, five);
    /// solver.assert_term(eq);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    ///
    /// if let Some(model_str) = solver.model_str() {
    ///     assert!(model_str.contains("define-fun"));
    /// }
    /// ```
    #[must_use]
    pub fn model_str(&self) -> Option<String> {
        self.try_get_model_str().ok()
    }

    /// Deprecated: use [`model_str`](Self::model_str) instead.
    #[deprecated(since = "0.3.0", note = "Use model_str() instead")]
    #[must_use]
    pub fn get_model_str(&self) -> Option<String> {
        self.model_str()
    }

    /// Fallible version of [`model_str`](Self::model_str).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotSat`] — last result was not Sat
    /// - [`SolverError::ModelGenerationFailed`] — executor returned empty or error model
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_model_str(&self) -> Result<String, SolverError> {
        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if last_result != SolveResult::Sat {
            return Err(SolverError::NotSat);
        }

        let model_str = self.executor.model();
        if model_str.is_empty() {
            return Err(SolverError::ModelGenerationFailed(
                "empty model string".into(),
            ));
        }
        if model_str.starts_with("(error ") {
            return Err(SolverError::ModelGenerationFailed(model_str));
        }
        Ok(model_str)
    }

    /// Model from the last SAT result.
    ///
    /// Returns None if the last check_sat did not return Sat.
    /// Returns a [`VerifiedModel`] that proves the model came from a validated
    /// solve path.
    #[must_use]
    pub fn model(&self) -> Option<VerifiedModel> {
        self.try_get_model().ok()
    }

    /// Deprecated: use [`model`](Self::model) instead.
    #[deprecated(since = "0.3.0", note = "Use model() instead")]
    #[must_use]
    pub fn get_model(&self) -> Option<VerifiedModel> {
        self.model()
    }

    /// Fallible version of [`model`](Self::model).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotSat`] — last result was not Sat
    /// - [`SolverError::ModelGenerationFailed`] — executor returned empty or error model
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_model(&self) -> Result<VerifiedModel, SolverError> {
        let model_str = self.try_get_model_str()?;
        Ok(VerifiedModel::from_validated(model_parse::parse_model_str(
            &model_str,
        )))
    }

    /// Iterate variables declared through [`Self::declare_const`].
    ///
    /// Fresh variables created with [`Self::fresh_var`] are intentionally excluded.
    pub fn declared_variables(&self) -> impl Iterator<Item = (&str, Term)> + '_ {
        let mut vars: Vec<_> = self.var_names.iter().collect();
        vars.sort_unstable_by_key(|(term_id, _)| term_id.0);
        vars.into_iter()
            .map(|(term_id, name)| (name.as_str(), Term(*term_id)))
    }

    /// Structured model map for all declared variables.
    ///
    /// The result maps declared variable names to `ModelValue` entries.
    /// Returns `None` unless the last result was SAT and value extraction succeeds.
    #[must_use]
    pub fn model_map(&self) -> Option<HashMap<String, ModelValue>> {
        self.try_get_model_map().ok()
    }

    /// Deprecated: use [`model_map`](Self::model_map) instead.
    #[deprecated(since = "0.3.0", note = "Use model_map() instead")]
    #[must_use]
    pub fn get_model_map(&self) -> Option<HashMap<String, ModelValue>> {
        self.model_map()
    }

    /// Fallible version of [`model_map`](Self::model_map).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotSat`] — last result was not Sat
    /// - [`SolverError::ModelGenerationFailed`] — value extraction failed
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_model_map(&self) -> Result<HashMap<String, ModelValue>, SolverError> {
        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if last_result != SolveResult::Sat {
            return Err(SolverError::NotSat);
        }

        let declared: Vec<_> = self
            .declared_variables()
            .map(|(name, term)| (name.to_string(), term))
            .collect();
        if declared.is_empty() {
            // Preserve the valid empty-model case without masking disabled
            // model generation or other executor-side failures.
            self.try_get_model_str()?;
            return Ok(HashMap::new());
        }

        let terms: Vec<_> = declared.iter().map(|(_, term)| *term).collect();
        let values = self.try_get_values(&terms)?;
        let mut model: HashMap<String, ModelValue> = Default::default();
        for ((name, _), value) in declared.into_iter().zip(values.into_iter()) {
            model.insert(name, value);
        }
        Ok(model)
    }

    /// Value of a single term in the current model.
    ///
    /// This uses the SMT-LIB `(get-value ...)` command to retrieve the value
    /// of the given term. The term can be any expression, not just a variable.
    ///
    /// Returns `None` if:
    /// - The last check_sat did not return Sat
    /// - The solver failed to evaluate the term
    ///
    /// # Example
    ///
    /// ```
    /// # use z4_dpll::api::{Solver, Sort, Logic, SolveResult, ModelValue};
    /// # use num_bigint::BigInt;
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.int_var("x");
    /// let five = solver.int_const(5);
    /// let eq = solver.eq(x, five);
    /// solver.assert_term(eq);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    ///
    /// if let Some(ModelValue::Int(val)) = solver.value(x) {
    ///     assert_eq!(val, BigInt::from(5));
    /// }
    /// ```
    #[must_use]
    pub fn value(&self, term: Term) -> Option<ModelValue> {
        self.try_get_value(term).ok()
    }

    /// Deprecated: use [`value`](Self::value) instead.
    #[deprecated(since = "0.3.0", note = "Use value() instead")]
    #[must_use]
    pub fn get_value(&self, term: Term) -> Option<ModelValue> {
        self.value(term)
    }

    /// Fallible version of [`value`](Self::value).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotSat`] — last result was not Sat
    /// - [`SolverError::ModelGenerationFailed`] — value extraction failed
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_value(&self, term: Term) -> Result<ModelValue, SolverError> {
        let mut values = self.try_get_values(&[term])?;
        Ok(values
            .pop()
            .expect("invariant: try_get_values returns one value per input term"))
    }

    /// Values of multiple terms in the current model.
    ///
    /// This uses the SMT-LIB `(get-value ...)` command to retrieve values
    /// for all given terms in a single query.
    ///
    /// Returns `None` if:
    /// - The last check_sat did not return Sat
    /// - The solver failed to evaluate the terms
    ///
    /// # Example
    ///
    /// ```
    /// # use z4_dpll::api::{Solver, Sort, Logic, SolveResult, ModelValue};
    /// # use num_bigint::BigInt;
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.int_var("x");
    /// let y = solver.int_var("y");
    /// let sum = solver.add(x, y);
    /// let ten = solver.int_const(10);
    /// let eq = solver.eq(sum, ten);
    /// solver.assert_term(eq);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    ///
    /// if let Some(values) = solver.values(&[x, y, sum]) {
    ///     // x + y = 10, sum = 10
    ///     if let ModelValue::Int(s) = &values[2] {
    ///         assert_eq!(*s, BigInt::from(10));
    ///     }
    /// }
    /// ```
    #[must_use]
    pub fn values(&self, terms: &[Term]) -> Option<Vec<ModelValue>> {
        self.try_get_values(terms).ok()
    }

    /// Deprecated: use [`values`](Self::values) instead.
    #[deprecated(since = "0.3.0", note = "Use values() instead")]
    #[must_use]
    pub fn get_values(&self, terms: &[Term]) -> Option<Vec<ModelValue>> {
        self.values(terms)
    }

    /// Fallible version of [`values`](Self::values).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] — no `check_sat` has been called
    /// - [`SolverError::NotSat`] — last result was not Sat
    /// - [`SolverError::ModelGenerationFailed`] — value extraction failed
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_get_values(&self, terms: &[Term]) -> Result<Vec<ModelValue>, SolverError> {
        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if last_result != SolveResult::Sat {
            return Err(SolverError::NotSat);
        }

        if terms.is_empty() {
            return Ok(Vec::new());
        }

        let term_ids: Vec<TermId> = terms.iter().map(|t| t.0).collect();
        let output = self.executor.values(&term_ids);

        if output.starts_with("(error ") || output.is_empty() {
            return Err(SolverError::ModelGenerationFailed(output));
        }

        model_parse::parse_get_value_output(&output, terms, self.terms()).ok_or_else(|| {
            SolverError::ModelGenerationFailed(format!(
                "failed to parse get-value output: {output}"
            ))
        })
    }

    /// Raw SMT-LIB output from `(get-value ...)`.
    ///
    /// Returns the unparsed output string, useful for debugging or custom parsing.
    #[must_use]
    pub fn values_smtlib(&self, terms: &[Term]) -> Option<String> {
        let last_result = self.executor.last_result()?;
        if last_result != SolveResult::Sat {
            return None;
        }

        if terms.is_empty() {
            return Some("()".to_string());
        }

        let term_ids: Vec<TermId> = terms.iter().map(|t| t.0).collect();
        let output = self.executor.values(&term_ids);

        if output.starts_with("(error ") || output.is_empty() {
            return None;
        }

        Some(output)
    }

    /// Deprecated: use [`values_smtlib`](Self::values_smtlib) instead.
    #[deprecated(since = "0.3.0", note = "Use values_smtlib() instead")]
    #[must_use]
    pub fn get_values_smtlib(&self, terms: &[Term]) -> Option<String> {
        self.values_smtlib(terms)
    }
}
