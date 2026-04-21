// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-term observation logic for model validation.
//!
//! Contains `validate_term_observation` (the per-assertion/assumption evaluator),
//! `apply_assumption_observation`, and `validate_sat_assumptions`.
//!
//! Extracted from `pipeline.rs` for code health (#5970).

use z4_core::{Sort, TermId, VerificationBoundary, VerificationVerdict};

use super::{
    ValidationObservation, ValidationSkipKind, ValidationTarget, TERM_FLAG_ARRAY, TERM_FLAG_BV_CMP,
    TERM_FLAG_DATATYPE, TERM_FLAG_INTERNAL, TERM_FLAG_QUANTIFIER, TERM_FLAG_SEQ, TERM_FLAG_STRING,
};
use crate::executor::model::{EvalValue, Executor, Model};
use crate::executor_types::{ModelValidationError, SolveResult};

impl Executor {
    pub(in crate::executor::model) fn validate_term_observation(
        &self,
        model: &Model,
        term: TermId,
        index: usize,
        flags: u8,
        has_array_assertions: bool,
        target: ValidationTarget,
    ) -> ValidationObservation {
        if flags & TERM_FLAG_INTERNAL != 0 {
            return ValidationObservation::Skip(ValidationSkipKind::Internal);
        }
        if flags & TERM_FLAG_QUANTIFIER != 0 {
            return ValidationObservation::Skip(ValidationSkipKind::Quantifier);
        }

        let has_datatype = flags & TERM_FLAG_DATATYPE != 0;
        if has_datatype && flags & TERM_FLAG_BV_CMP == 0 {
            let term_str = self.format_term(term);
            return match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => ValidationObservation::independent(target, true),
                EvalValue::Bool(false) => ValidationObservation::violated(
                    target,
                    format!(
                        "{}: {term_str} evaluates to false (datatype)",
                        target.violated_entry(index),
                    ),
                ),
                _ if matches!(target, ValidationTarget::GroundAssertion) => {
                    ValidationObservation::Skip(ValidationSkipKind::Datatype)
                }
                _ => ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} datatype assumption evaluates to Unknown",
                        target.entry(index),
                    ),
                ),
            };
        }

        if has_datatype {
            let term_str = self.format_term(term);
            return match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => ValidationObservation::independent(target, true),
                _ if matches!(target, ValidationTarget::GroundAssertion) => {
                    if self.sat_term_assigned_true(model, term) {
                        ValidationObservation::fallback(format!(
                            "{}: {term_str} used SAT-fallback for DT+BV validation",
                            target.entry(index),
                        ))
                    } else {
                        ValidationObservation::Skip(ValidationSkipKind::Dtbv)
                    }
                }
                _ => ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} datatype assumption evaluates to Unknown",
                        target.entry(index),
                    ),
                ),
            };
        }

        if matches!(target, ValidationTarget::GroundAssertion) && flags & TERM_FLAG_SEQ != 0 {
            let term_str = self.format_term(term);
            match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => {
                    return ValidationObservation::independent(target, false);
                }
                EvalValue::Bool(false) => {
                    return ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} evaluates to false (seq theory)",
                            target.entry(index),
                        ),
                    );
                }
                _ => {}
            }
        }

        if matches!(target, ValidationTarget::GroundAssertion)
            && flags & TERM_FLAG_STRING != 0
            && model.string_model.is_some()
        {
            let term_str = self.format_term(term);
            match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => {
                    return ValidationObservation::independent(target, false);
                }
                EvalValue::Bool(false) => {
                    // String model extraction is incomplete: the CEGAR loop
                    // may not propagate all variable assignments into the
                    // string model (e.g., pivot enum variables, cross-theory
                    // equalities). If the SAT solver's truth assignment says
                    // the assertion is true, treat this as a model extraction
                    // gap rather than a soundness violation (#7460).
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {term_str} string evaluation false but SAT-assigned true",
                            target.entry(index),
                        ));
                    }
                    return ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} evaluates to false (string theory)",
                            target.violated_entry(index),
                        ),
                    );
                }
                _ if self.sat_term_assigned_true(model, term) => {
                    return ValidationObservation::delegated();
                }
                _ => {}
            }
        }

        if matches!(target, ValidationTarget::Assumption)
            && matches!(self.ctx.terms.sort(term), Sort::Bool)
            && flags & TERM_FLAG_ARRAY == 0
            && self.sat_assumption_assigned_true(model, term)
        {
            return ValidationObservation::delegated();
        }

        // Defer format_term to avoid exponential DAG-to-tree blowup on success paths.
        // format_term has no memoization, so on deeply nested BV terms it can take
        // seconds even though the string is only needed for error messages.
        let term_str = || self.format_term(term);
        match self.evaluate_term(model, term) {
            EvalValue::Bool(true) => ValidationObservation::independent(target, false),
            EvalValue::Bool(false) => {
                if flags & TERM_FLAG_ARRAY != 0 {
                    // Array-containing assertions may evaluate to false due to
                    // incomplete model evaluation of select/store chains, not due
                    // to actual model violations. When the SAT solver assigns the
                    // assertion's Tseitin variable to true, the complete
                    // bit-blasted encoding IS satisfied. Accept SAT-fallback for
                    // any array-containing ground assertion (not just equalities).
                    if matches!(target, ValidationTarget::GroundAssertion)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used SAT-fallback for array validation (eval=false)",
                            target.entry(index), term_str(),
                        ));
                    }
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {} array {} evaluates to false",
                            target.entry(index), term_str(),
                            target.kind_name(),
                        ),
                    );
                }
                if matches!(target, ValidationTarget::GroundAssertion)
                    && self.arithmetic_false_may_be_model_extraction_gap(model, term)
                    && self.sat_term_assigned_true(model, term)
                {
                    return ValidationObservation::fallback(format!(
                        "{}: {} arithmetic evaluation false but SAT-assigned true",
                        target.entry(index), term_str(),
                    ));
                }
                ValidationObservation::violated(
                    target,
                    format!(
                        "{}: {} evaluates to false",
                        target.violated_entry(index), term_str(),
                    ),
                )
            }
            EvalValue::Unknown => {
                if matches!(target, ValidationTarget::GroundAssertion) {
                    if self.is_pure_boolean_formula(term)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::delegated();
                    }
                    if flags & TERM_FLAG_ARRAY != 0 {
                        if self.sat_term_assigned_true(model, term) {
                            return ValidationObservation::fallback(format!(
                                "{}: {} used SAT-fallback for array validation",
                                target.entry(index), term_str(),
                            ));
                        }
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} array assertion evaluates to Unknown",
                                target.entry(index), term_str(),
                            ),
                        );
                    }
                    if self.is_arithmetic_boolean_assertion(term)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used SAT-fallback for arithmetic validation",
                            target.entry(index), term_str(),
                        ));
                    }
                    if self.is_arithmetic_boolean_assertion(term) && has_array_assertions {
                        return ValidationObservation::Skip(ValidationSkipKind::ArithArrayMix);
                    }
                    if flags & TERM_FLAG_BV_CMP != 0 && model.bv_model.is_none() {
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} contains BV comparison without BV model (AUFLIA routing)",
                                target.entry(index), term_str(),
                            ),
                        );
                    }
                    if flags & TERM_FLAG_BV_CMP != 0 {
                        let is_pure_bv = flags
                            & (TERM_FLAG_ARRAY
                                | TERM_FLAG_SEQ
                                | TERM_FLAG_DATATYPE
                                | TERM_FLAG_QUANTIFIER)
                            == 0;
                        if is_pure_bv {
                            return ValidationObservation::incomplete(
                                target,
                                format!(
                                    "{}: {} pure BV assertion evaluates to Unknown with BV model present",
                                    target.entry(index), term_str(),
                                ),
                            );
                        }
                        if self.sat_term_assigned_true(model, term) {
                            return ValidationObservation::fallback(format!(
                                "{}: {} used SAT-fallback for mixed BV validation",
                                target.entry(index), term_str(),
                            ));
                        }
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} contains BV comparison predicate with Unknown value",
                                target.entry(index), term_str(),
                            ),
                        );
                    }
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used generic SAT-fallback",
                            target.entry(index), term_str(),
                        ));
                    }
                }
                ValidationObservation::incomplete(
                    target,
                    format!("{}: {} evaluates to Unknown", target.entry(index), term_str()),
                )
            }
            EvalValue::Element(_)
            | EvalValue::Rational(_)
            | EvalValue::BitVec { .. }
            | EvalValue::Fp(_)
            | EvalValue::String(_)
            | EvalValue::Seq(_) => ValidationObservation::violated(
                target,
                format!("{} has non-Boolean value: {}", target.entry(index), term_str()),
            ),
        }
    }

    fn apply_assumption_observation(
        accepted_assumptions: &mut usize,
        skipped_internal: &mut usize,
        skipped_quantifier: &mut usize,
        observation: ValidationObservation,
    ) -> Result<(), ModelValidationError> {
        match observation {
            ValidationObservation::Skip(kind) => match kind {
                ValidationSkipKind::Internal => {
                    *skipped_internal += 1;
                    Ok(())
                }
                ValidationSkipKind::Quantifier => {
                    *skipped_quantifier += 1;
                    Ok(())
                }
                other => Err(ModelValidationError::incomplete(
                    VerificationBoundary::SmtAssumption,
                    format!("unsupported assumption skip category: {other:?}"),
                )),
            },
            ValidationObservation::Fallback(failure) => {
                Err(ModelValidationError::Incomplete(failure))
            }
            ValidationObservation::Verdict { verdict, .. } => match verdict {
                VerificationVerdict::Verified { .. } => {
                    *accepted_assumptions += 1;
                    Ok(())
                }
                VerificationVerdict::Incomplete(failure) => {
                    Err(ModelValidationError::Incomplete(failure))
                }
                VerificationVerdict::Violated(failure) => {
                    Err(ModelValidationError::Violated(failure))
                }
                _ => {
                    unreachable!("unexpected verification verdict variant in assumption validation")
                }
            },
        }
    }

    /// Validate temporary assumptions used by `check_sat_assuming`.
    pub(in crate::executor::model) fn validate_sat_assumptions(
        &self,
        assumptions: &[TermId],
    ) -> Result<(), ModelValidationError> {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                if assumptions.is_empty() {
                    return Ok(());
                }
                return Err(ModelValidationError::incomplete(
                    VerificationBoundary::SmtAssumption,
                    "no model available",
                ));
            }
            _ => {
                return Err(ModelValidationError::violated(
                    VerificationBoundary::SmtAssumption,
                    "Assumption validation requires SAT result",
                ))
            }
        };

        let mut accepted_assumptions = 0usize;
        let mut skipped_internal = 0usize;
        let mut skipped_quantifier = 0usize;
        let term_flags = self.precompute_term_flags();

        for (i, &assumption) in assumptions.iter().enumerate() {
            let observation = self.validate_term_observation(
                model,
                assumption,
                i,
                term_flags[assumption.index()],
                false,
                ValidationTarget::Assumption,
            );
            Self::apply_assumption_observation(
                &mut accepted_assumptions,
                &mut skipped_internal,
                &mut skipped_quantifier,
                observation,
            )?;
        }

        if accepted_assumptions == 0 && skipped_internal > 0 {
            return Err(ModelValidationError::incomplete(
                VerificationBoundary::SmtAssumption,
                format!(
                    "all {} assumptions were skipped or unevaluable \
                     (internal={}, quantifier={})",
                    assumptions.len(),
                    skipped_internal,
                    skipped_quantifier,
                ),
            ));
        }

        Ok(())
    }
}
